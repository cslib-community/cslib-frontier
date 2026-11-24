/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.SmallRegime
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.SplitPairProg
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargePageCoreProg
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargePageProg
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeBlockPool
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpochState
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Accessors
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.SmallRegime
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.SplitPairProg
-- Private page-arena helpers shared across the LargePageBaseProg/LargePageCoreProg split.
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargePageBaseProg
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargePageCoreProg
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargePageProg
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpochState

/-!
# Memory History Admissibility (`ValidHistory`) for Pair, Page-Arena, and Small-Epoch Programs

This module proves `(Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p)` (under
`Memory.WellFormed w s` and the layout/precondition predicate matching each `RealizesBounded .exact`
certificate) for the public `Memory.Prog` operations of `SmallRegime`, `SplitPairProg`,
`LargePageBaseProg`, `LargePageCoreProg`, `LargePageProg`, `SlotIoLayout` (`LargeBlockPool`), and
the small-regime epoch operations of `LargeEpochState`.

It uses private `import all` solely to unfold the unexposed `Memory.Prog` bodies of those modules
without modifying existing library modules or invalidating cached `.olean` artifacts.

## Main results

* `validHistory_readPairGenProg`, `validHistory_writePairGenProg`, `validHistory_swapPairGenProg`,
  `validHistory_smallScanStepProg`, `validHistory_smallScanGenProg`,
  `validHistory_smallDeleteSwapGenProg`: pair-stream and small-array accessors (`SmallRegime`).
* `validHistory_splitPairReadProg`, `validHistory_splitPairWriteProg`,
  `validHistory_slideUpStepProg`, `validHistory_slideUpBatchProg`,
  `validHistory_slideDownStepProg`, `validHistory_slideDownBatchProg`,
  `validHistory_zeroWordsStepProg`, `validHistory_zeroWordsBatchProg`: split-pair sliding and
  batched word zeroing (`SplitPairProg`).
* `validHistory_pageInitScalarsProg`, `validHistory_pageInitDirBatchProg`,
  `validHistory_pageInitTailBatchProg`, `validHistory_pageReadVirtBoundedProg`,
  `validHistory_pageWriteVirtBoundedProg`, `validHistory_pageSwapPhysProg`,
  `validHistory_pageRunTicksBatchProg`, `validHistory_pageBeginUnpermBoundedProg`,
  `validHistory_pageUnpermStepBoundedProg`, `validHistory_pageRunUnpermBatchProg`,
  `validHistory_pageAppendBoundedProg`, `validHistory_pagePopBackBoundedProg`: bit-packed page
  arena and unpermutation (`LargePageBaseProg`, `LargePageCoreProg`, `LargePageProg`).
* `validHistory_slotIoReadRawProg`, `validHistory_slotIoWriteRawProg`,
  `validHistory_slotIoSwapRawProg`, `validHistory_slotIoAppendRawProg`,
  `validHistory_slotIoPopBackRawProg`: unified `SlotIoLayout` wrappers (`LargeBlockPool`).
* `validHistory_smallEpochInitProg`, `validHistory_smallEpochQueryRawProg`,
  `validHistory_smallEpochInsertRawProg`, `validHistory_smallEpochDeleteRawProg`,
  `validHistory_smallEpochPopAnyRawProg`: small-regime epoch operations (`LargeEpochState`).
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.WordRAM.Resizable
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct

/-! ## Section 1: Generic `ValidHistory` Combinators -/

private theorem wellFormed_clientState {α : Type} {w : ℕ} {s : Memory.State}
    {p : Memory.Prog α} (hwf : Memory.WellFormed w s)
    (hp : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p)) :
    Memory.WellFormed w ((Memory.spec 0).clientState s p) := by
  rw [← clientState_width w, ← (Memory.spec w).run_runClient p s]
  exact hwf.run hp

private theorem frontier_le_clientState {α : Type} {s : Memory.State} (p : Memory.Prog α) :
    s.frontier ≤ ((Memory.spec 0).clientState s p).frontier := by
  rw [← (Memory.spec 0).run_runClient p s]
  exact Memory.frontier_le_run s _

private theorem validHistory_bind_eq {α β : Type} {w : ℕ} {s : Memory.State}
    {p : Memory.Prog α} {q : α → Memory.Prog β}
    (hp : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p))
    (hq : (Memory.spec w).ValidHistory ((Memory.spec 0).clientState s p)
      ((Memory.spec w).clientHistory ((Memory.spec 0).clientState s p)
        (q ((Memory.spec 0).clientResult s p)))) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p >>= q)) := by
  change (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p.bind q))
  rw [validHistory_bind, clientResult_width, clientState_width]
  exact ⟨hp, hq⟩

private theorem validHistory_bind_ro {α β : Type} {w : ℕ} {s : Memory.State}
    {p : Memory.Prog α} {q : α → Memory.Prog β}
    (hp : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p))
    (hq : ∀ a s', s.frontier ≤ s'.frontier →
      (Memory.spec w).ValidHistory s' ((Memory.spec w).clientHistory s' (q a))) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p >>= q)) :=
  validHistory_bind_eq hp (hq _ _ (frontier_le_clientState p))

private theorem validHistory_bind_wf {α β : Type} {w : ℕ} {s : Memory.State}
    {p : Memory.Prog α} {q : α → Memory.Prog β}
    (hwf : Memory.WellFormed w s)
    (hp : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p))
    (hq : ∀ a s', Memory.WellFormed w s' → s.frontier ≤ s'.frontier →
      (Memory.spec w).ValidHistory s' ((Memory.spec w).clientHistory s' (q a))) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p >>= q)) :=
  validHistory_bind_eq hp (hq _ _ (wellFormed_clientState hwf hp) (frontier_le_clientState p))

private theorem validHistory_read_bind {α : Type} {w a : ℕ} {s : Memory.State}
    {q : ℕ → Memory.Prog α} (ha : a < s.frontier)
    (hq : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (q (s.mem a)))) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (Memory.read a >>= q)) :=
  validHistory_bind_eq ⟨ha, trivial⟩ hq

private theorem validHistory_read_bind_wf {α : Type} {w a : ℕ} {s : Memory.State}
    {q : ℕ → Memory.Prog α} (hwf : Memory.WellFormed w s) (ha : a < s.frontier)
    (hq : ∀ x : ℕ, x < 2 ^ w →
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (q x))) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (Memory.read a >>= q)) :=
  validHistory_bind_eq ⟨ha, trivial⟩ (hq (s.mem a) (hwf.2 a))

private theorem validHistory_write_only {w a v : ℕ} {s : Memory.State}
    (ha : a < s.frontier) (hv : v < 2 ^ w) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (Memory.write a v)) :=
  ⟨⟨ha, hv⟩, trivial⟩

private theorem validHistory_write_bind {α : Type} {w a v : ℕ} {s : Memory.State}
    {q : Unit → Memory.Prog α} (ha : a < s.frontier) (hv : v < 2 ^ w)
    (hq : ∀ s' : Memory.State, s'.frontier = s.frontier →
      (Memory.spec w).ValidHistory s' ((Memory.spec w).clientHistory s' (q ()))) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (Memory.write a v >>= q)) :=
  validHistory_bind_eq ⟨⟨ha, hv⟩, trivial⟩ (hq _ rfl)

private theorem validHistory_write_bind_wf {α : Type} {w a v : ℕ} {s : Memory.State}
    {q : Unit → Memory.Prog α} (hwf : Memory.WellFormed w s)
    (ha : a < s.frontier) (hv : v < 2 ^ w)
    (hq : ∀ s' : Memory.State, Memory.WellFormed w s' → s'.frontier = s.frontier →
      (Memory.spec w).ValidHistory s' ((Memory.spec w).clientHistory s' (q ()))) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (Memory.write a v >>= q)) :=
  validHistory_bind_eq ⟨⟨ha, hv⟩, trivial⟩ (hq _ (hwf.step (o := .write a v) ⟨ha, hv⟩) rfl)

private theorem validHistory_ite {α : Type} {w : ℕ} {s : Memory.State}
    (P : Prop) [Decidable P] {p₁ p₂ : Memory.Prog α}
    (h₁ : P → (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p₁))
    (h₂ : ¬P → (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p₂)) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (if P then p₁ else p₂)) := by
  by_cases hP : P
  · rw [ite_eq_left hP]; exact h₁ hP
  · rw [ite_eq_right hP]; exact h₂ hP

private theorem validHistory_iterate_inv {δ σ : Type} {w : ℕ}
    {body : δ × σ → Memory.Prog σ} {Inv : σ → Memory.State → Prop}
    {d : δ} (fuel : ℕ) (a : σ) (s : Memory.State)
    (hinv : Inv a s)
    (hstep : ∀ a' s', Inv a' s' →
      (Memory.spec w).ValidHistory s' ((Memory.spec w).clientHistory s' (body (d, a'))))
    (hnext : ∀ a' s', Inv a' s' →
      (Memory.spec w).ValidHistory s' ((Memory.spec w).clientHistory s' (body (d, a'))) →
      Inv ((Memory.spec 0).clientResult s' (body (d, a')))
        ((Memory.spec 0).clientState s' (body (d, a')))) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (iterate body d fuel a)) := by
  induction fuel generalizing a s with
  | zero => exact trivial
  | succ k ih =>
    unfold iterate
    have h1 := hstep a s hinv
    exact validHistory_bind_eq h1 (ih _ _ (hnext a s hinv h1))

private theorem validHistory_iterate_wf {δ σ : Type} {w : ℕ}
    {body : δ × σ → Memory.Prog σ} {d : δ} (fuel : ℕ) (a : σ) (s : Memory.State)
    {P : Memory.State → Prop} (hwf : Memory.WellFormed w s) (hP : P s)
    (hmono : ∀ s₁ s₂ : Memory.State, s₁.frontier ≤ s₂.frontier → P s₁ → P s₂)
    (hstep : ∀ a' s', Memory.WellFormed w s' → P s' →
      (Memory.spec w).ValidHistory s' ((Memory.spec w).clientHistory s' (body (d, a')))) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (iterate body d fuel a)) :=
  validHistory_iterate_inv (Inv := fun _ s' => Memory.WellFormed w s' ∧ P s') fuel a s
    ⟨hwf, hP⟩
    (fun a' s' ⟨hwf', hP'⟩ => hstep a' s' hwf' hP')
    (fun _ s' ⟨hwf', hP'⟩ h1 =>
      ⟨wellFormed_clientState hwf' h1, hmono s' _ (frontier_le_clientState _) hP'⟩)

private theorem pageArenaValid_mono {L : PageArenaLayout} {w f₁ f₂ : ℕ}
    (hv : L.Valid w f₁) (hle : f₁ ≤ f₂) : L.Valid w f₂ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := hv
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15.trans hle⟩

private theorem splitPairValid_mono {cfg : SplitPairCfg} {w n_tot f₁ f₂ : ℕ}
    (hv : cfg.Valid w n_tot f₁) (hle : f₁ ≤ f₂) : cfg.Valid w n_tot f₂ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hv
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10.trans hle⟩

private theorem slotIoValid_mono {io : SlotIoLayout} {w f₁ f₂ : ℕ}
    (hv : io.Valid w f₁) (hle : f₁ ≤ f₂) : io.Valid w f₂ := by
  unfold SlotIoLayout.Valid at hv ⊢
  by_cases h0 : io.usePaged = 0
  · rw [ite_eq_left h0] at hv ⊢
    obtain ⟨h1, h2, h3, h4, h5, htail⟩ := hv
    refine ⟨h1, h2, h3, h4, h5, ?_⟩
    by_cases hs : io.sideBit = 0
    · rw [ite_eq_left hs] at htail ⊢; exact htail.trans hle
    · rw [ite_eq_right hs] at htail ⊢
      obtain ⟨ha, hb, hc, hd, he⟩ := htail
      exact ⟨ha, hb, hc, hd, he.trans hle⟩
  · rw [ite_eq_right h0] at hv ⊢
    exact pageArenaValid_mono hv hle

private theorem pageArenaValid_meta32 {L : PageArenaLayout} {w fr : ℕ}
    (hv : L.Valid w fr) : L.metaBase + 32 ≤ fr := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, ho1, ho2, hm_ib, hib_fr⟩ := hv
  omega

private theorem pageArenaValid_pg16_lt {L : PageArenaLayout} {w fr : ℕ}
    (hv : L.Valid w fr) : 16 * L.pgB < 2 ^ w := by
  obtain ⟨_, _, hpb, _, _, _, hpg16, _, _, _, _, _, _, _, _⟩ := hv
  exact lt_of_lt_of_le hpg16 (Nat.pow_le_pow_right two_pos hpb)

private theorem pageArenaValid_mp4_lt {L : PageArenaLayout} {w fr : ℕ}
    (hv : L.Valid w fr) : 4 * L.maxPages < 2 ^ w := by
  obtain ⟨_, _, hpb, _, _, _, _, _, hmp4, _, _, _, _, _, _⟩ := hv
  exact lt_of_lt_of_le hmp4 (Nat.pow_le_pow_right two_pos hpb)

private theorem pageArenaValid_const_lt {L : PageArenaLayout} {w fr : ℕ}
    (hv : L.Valid w fr) : 32 < 2 ^ w := by
  have hpg32 : 32 ≤ L.pgB := hv.2.2.2.2.2.1
  have hpg16 := pageArenaValid_pg16_lt hv
  omega

private theorem slotIoValid_nCap_lt {io : SlotIoLayout} {w fr : ℕ}
    (hv : io.Valid w fr) : io.pgL.nCap < 2 ^ w := by
  unfold SlotIoLayout.Valid at hv
  by_cases h0 : io.usePaged = 0
  · rw [ite_eq_left h0] at hv
    exact hv.2.2.2.2.1
  · rw [ite_eq_right h0] at hv
    exact hv.2.2.2.2.2.2.2.2.2.2.1

private theorem packedWords_pos (n k w : ℕ) : 2 ≤ packedWords n k w := by
  unfold packedWords; exact Nat.le_add_left 2 _

private theorem pairStreamWords_ge_two (n qB vB w : ℕ) :
    2 ≤ pairStreamWords n qB vB w :=
  packedWords_pos n (qB + vB) w

private theorem validHistory_bind_page {α β : Type} {w : ℕ} {ctx : PageArenaCtx}
    {s : Memory.State} {p : Memory.Prog α} {q : α → Memory.Prog β}
    (hwf : Memory.WellFormed w s) (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier)
    (hp : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p))
    (hq : ∀ a s', Memory.WellFormed w s' → (PageArenaLayout.ofCtx ctx).Valid w s'.frontier →
      (Memory.spec w).ValidHistory s' ((Memory.spec w).clientHistory s' (q a))) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p >>= q)) :=
  validHistory_bind_wf hwf hp fun a s' hwf' hfr => hq a s' hwf' (pageArenaValid_mono hv hfr)

private theorem validHistory_bind_page_ro {α β : Type} {w : ℕ} {ctx : PageArenaCtx}
    {s : Memory.State} {p : Memory.Prog α} {q : α → Memory.Prog β}
    (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier)
    (hp : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p))
    (hq : ∀ a s', (PageArenaLayout.ofCtx ctx).Valid w s'.frontier →
      (Memory.spec w).ValidHistory s' ((Memory.spec w).clientHistory s' (q a))) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p >>= q)) :=
  validHistory_bind_ro hp fun a s' hfr => hq a s' (pageArenaValid_mono hv hfr)

/-! ## Section 2: `SmallRegime` Pair-Stream and Small-Array Programs -/

/-- Memory history admissibility for `readPairGenProg`. -/
theorem validHistory_readPairGenProg {w : ℕ} {d : ((ℕ × (ℕ × ℕ)) × ℕ) × ℕ} {s : Memory.State}
    (h : ReadPairPre w d s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (readPairGenProg d)) := by
  rcases d with ⟨⟨⟨itemBase, ⟨q_bits, v_bits⟩⟩, wVal⟩, idx⟩
  obtain ⟨hw, rfl, hq, hv, hfr⟩ := h
  unfold readPairGenProg
  dsimp only
  refine validHistory_bind_eq (by unfold compQOffsetProg; trivial) ?_
  rw [clientState_compQOffsetProg, clientResult_compQOffsetProg]
  simp only [pure_bind]
  have hleQV := wOffQ_le_wOffV q_bits v_bits w idx
  refine validHistory_bind_ro
    (validHistory_readBitSliceGen ⟨hw, rfl, hq, bOffQ_lt hw, by omega⟩)
    fun _ s₁ hfr₁ => ?_
  have hbV : (bOffQ q_bits v_bits w idx + q_bits) % w < w :=
    bOffV_lt (q_bits := q_bits) (v_bits := v_bits) (d := idx) hw
  have hfrV : itemBase + (wOffQ q_bits v_bits w idx +
      (bOffQ q_bits v_bits w idx + q_bits) / w) + 1 < s₁.frontier := by
    have hlt := lt_of_lt_of_le hfr hfr₁
    simpa only [wOffV] using hlt
  exact validHistory_bind_ro
    (validHistory_readBitSliceGen ⟨hw, rfl, hv, hbV, hfrV⟩) fun _ _ _ => trivial

/-- Memory history admissibility for `writePairGenProg`. -/
theorem validHistory_writePairGenProg {w : ℕ}
    {d : (((ℕ × (ℕ × ℕ)) × ℕ) × ℕ) × (ℕ × ℕ)} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (h : WritePairPre w d s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (writePairGenProg d)) := by
  rcases d with ⟨⟨⟨⟨itemBase, ⟨q_bits, v_bits⟩⟩, wVal⟩, idx⟩, ⟨q, v⟩⟩
  obtain ⟨hw, rfl, hq, hv, hfr⟩ := h
  unfold writePairGenProg
  dsimp only
  refine validHistory_bind_eq (by unfold compQOffsetProg; trivial) ?_
  rw [clientState_compQOffsetProg, clientResult_compQOffsetProg]
  simp only [pure_bind]
  have hleQV := wOffQ_le_wOffV q_bits v_bits w idx
  refine validHistory_bind_wf hwf
    (validHistory_writeBitSliceGen hwf ⟨hw, rfl, hq, bOffQ_lt hw, by omega⟩)
    fun _ s₁ hwf₁ hfr₁ => ?_
  have hbV : (bOffQ q_bits v_bits w idx + q_bits) % w < w :=
    bOffV_lt (q_bits := q_bits) (v_bits := v_bits) (d := idx) hw
  have hfrV : itemBase + (wOffQ q_bits v_bits w idx +
      (bOffQ q_bits v_bits w idx + q_bits) / w) + 1 < s₁.frontier := by
    have hlt := lt_of_lt_of_le hfr hfr₁
    simpa only [wOffV] using hlt
  exact validHistory_writeBitSliceGen hwf₁ ⟨hw, rfl, hv, hbV, hfrV⟩

/-- Memory history admissibility for `swapPairGenProg`. -/
theorem validHistory_swapPairGenProg {w : ℕ} {d : ((ℕ × (ℕ × ℕ)) × ℕ) × (ℕ × ℕ)}
    {s : Memory.State} (hwf : Memory.WellFormed w s) (h : SwapPairPre w d s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (swapPairGenProg d)) := by
  rcases d with ⟨⟨⟨itemBase, ⟨q_bits, v_bits⟩⟩, wVal⟩, ⟨p₁, p₂⟩⟩
  obtain ⟨hw, rfl, hq, hv, hfr₁, hfr₂⟩ := h
  unfold swapPairGenProg
  dsimp only
  refine validHistory_ite (p₁ = p₂) (fun _ => trivial) (fun _ => ?_)
  refine validHistory_bind_wf hwf
    (validHistory_readPairGenProg ⟨hw, rfl, hq, hv, hfr₁⟩) fun _ s₁ hwf₁ hf₁ => ?_
  refine validHistory_bind_wf hwf₁
    (validHistory_readPairGenProg ⟨hw, rfl, hq, hv, lt_of_lt_of_le hfr₂ hf₁⟩)
    fun _ s₂ hwf₂ hf₂ => ?_
  refine validHistory_bind_wf hwf₂
    (validHistory_writePairGenProg hwf₂
      ⟨hw, rfl, hq, hv, lt_of_lt_of_le hfr₁ (hf₁.trans hf₂)⟩)
    fun _ s₃ hwf₃ hf₃ => ?_
  exact validHistory_writePairGenProg hwf₃
    ⟨hw, rfl, hq, hv, lt_of_lt_of_le hfr₂ (hf₁.trans (hf₂.trans hf₃))⟩

/-- Memory history admissibility for `smallScanStepProg`. -/
theorem validHistory_smallScanStepProg {w : ℕ} {d : SmallScanCtx × SmallScanAcc}
    {s : Memory.State} (h : SmallScanStepPre w d s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (smallScanStepProg d)) := by
  rcases d with ⟨⟨⟨⟨itemBase, ⟨q_bits, v_bits⟩⟩, wVal⟩, ⟨n, target⟩⟩,
    ⟨cur, ⟨found, ⟨idx, val⟩⟩⟩⟩
  obtain ⟨hw, rfl, hq, hv, hcur, _, _, _, _, hfr⟩ := h
  unfold smallScanStepProg
  dsimp only
  have hltV := wOffV_add_one_lt_pairStreamWords (q_bits := q_bits) (v_bits := v_bits) hw hcur
  refine validHistory_bind_ro
    (validHistory_readPairGenProg ⟨hw, rfl, hq, hv, by omega⟩) fun _ _ _ => ?_
  simp only [pure_bind]
  refine validHistory_ite (found = 0) (fun _ => ?_) (fun _ => trivial)
  exact validHistory_ite _ (fun _ => trivial) (fun _ => trivial)

/-- Memory history admissibility for `smallScanGenProg`. -/
theorem validHistory_smallScanGenProg {w : ℕ} {d : SmallScanCtx} {s : Memory.State}
    (h : SmallScanPre w d s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (smallScanGenProg d)) := by
  rcases d with ⟨⟨⟨itemBase, ⟨q_bits, v_bits⟩⟩, wVal⟩, ⟨n, target⟩⟩
  obtain ⟨hw, rfl, hq, hv, _hn_fit, hfr⟩ := h
  have hiter : ∀ k cur found idx val, cur + k ≤ n →
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
        (iterate smallScanStepProg (((itemBase, (q_bits, v_bits)), w), (n, target))
          k (cur, (found, (idx, val))))) := by
    intro k
    induction k with
    | zero => intro _ _ _ _ _; exact trivial
    | succ k ih =>
      intro cur found idx val hck
      unfold iterate
      have hcur : cur < n := by omega
      have hltV := wOffV_add_one_lt_pairStreamWords (q_bits := q_bits) (v_bits := v_bits) hw hcur
      have hstep : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
          (smallScanStepProg
            ((((itemBase, (q_bits, v_bits)), w), (n, target)),
              (cur, (found, (idx, val)))))) := by
        unfold smallScanStepProg; dsimp only
        refine validHistory_bind_ro
          (validHistory_readPairGenProg ⟨hw, rfl, hq, hv, by omega⟩) fun _ _ _ => ?_
        simp only [pure_bind]
        refine validHistory_ite (found = 0) (fun _ => ?_) (fun _ => trivial)
        exact validHistory_ite _ (fun _ => trivial) (fun _ => trivial)
      have hst : (Memory.spec 0).clientState s
          (smallScanStepProg
            ((((itemBase, (q_bits, v_bits)), w), (n, target)),
              (cur, (found, (idx, val))))) = s := by
        unfold smallScanStepProg; dsimp only
        rw [StateTransitionSpec.clientState_bind, clientState_readPairGenProg,
          clientResult_readPairGenProg]
        simp only [pure_bind]
        split_ifs <;> rfl
      refine validHistory_bind_eq hstep ?_
      rw [hst]
      have hfst : ((Memory.spec 0).clientResult s (smallScanStepProg
          ((((itemBase, (q_bits, v_bits)), w), (n, target)),
            (cur, (found, (idx, val)))))).1 = cur + 1 := by
        unfold smallScanStepProg; dsimp only
        rw [prog_clientResult_bind, clientState_readPairGenProg, clientResult_readPairGenProg]
        simp only [pure_bind]
        split_ifs <;> rfl
      rcases hres : (Memory.spec 0).clientResult s (smallScanStepProg
          ((((itemBase, (q_bits, v_bits)), w), (n, target)),
            (cur, (found, (idx, val))))) with ⟨cur', ⟨f', ⟨i', v'⟩⟩⟩
      rw [hres] at hfst
      exact ih cur' f' i' v' (by omega)
  unfold smallScanGenProg smallScanIterProg
  simp only [pure_bind]
  exact validHistory_bind_ro (hiter n 0 0 0 0 (by omega)) fun _ _ _ => trivial

/-- Memory history admissibility for `smallDeleteSwapGenProg`. -/
theorem validHistory_smallDeleteSwapGenProg {w : ℕ}
    {d : ((ℕ × (ℕ × ℕ)) × ℕ) × (ℕ × ℕ)} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (h : SmallDeleteSwapPre w d s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (smallDeleteSwapGenProg d)) := by
  rcases d with ⟨⟨⟨itemBase, ⟨q_bits, v_bits⟩⟩, wVal⟩, ⟨idx, n⟩⟩
  obtain ⟨hw, rfl, hq, hv, hidx, hfr⟩ := h
  unfold smallDeleteSwapGenProg
  simp only [pure_bind]
  refine validHistory_ite (idx < n - 1) (fun _ => ?_) (fun _ => trivial)
  have hlt_last := wOffV_add_one_lt_pairStreamWords
    (q_bits := q_bits) (v_bits := v_bits) hw (show n - 1 < n by omega)
  have hlt_idx := wOffV_add_one_lt_pairStreamWords
    (q_bits := q_bits) (v_bits := v_bits) hw hidx
  refine validHistory_bind_wf hwf
    (validHistory_readPairGenProg ⟨hw, rfl, hq, hv, by omega⟩) fun _ s₁ hwf₁ hf₁ => ?_
  exact validHistory_writePairGenProg hwf₁ ⟨hw, rfl, hq, hv, by omega⟩

/-! ## Section 3: `SplitPairProg` Programs -/

/-- Memory history admissibility for `splitPairReadProg`. -/
theorem validHistory_splitPairReadProg {w : ℕ} {d : (SplitPairCtx × ℕ) × ℕ} {s : Memory.State}
    (h : SplitPairReadPre w d s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (splitPairReadProg d)) := by
  rcases d with ⟨⟨⟨⟨⟨bL, ⟨qL, vL⟩⟩, ⟨bH, ⟨qH, vH⟩⟩⟩, wv⟩, s_split⟩, idx⟩
  obtain ⟨n_tot, hidx, hv⟩ := h
  have hv' := hv
  obtain ⟨hw, hwv, hqL, hvL, hqH, hvH, _, _, _, _⟩ := hv
  dsimp only [SplitPairCfg.ofCtx] at hwv hqL hvL hqH hvH
  subst hwv
  unfold splitPairReadProg
  refine validHistory_ite (idx < s_split) ?_ ?_
  · intro _
    exact validHistory_readPairGenProg ⟨hw, rfl, hqL, hvL, valid_lo_frontier hv' hidx⟩
  · intro _
    exact validHistory_readPairGenProg ⟨hw, rfl, hqH, hvH, valid_hi_frontier hv' hidx⟩

/-- Memory history admissibility for `splitPairWriteProg`. -/
theorem validHistory_splitPairWriteProg {w : ℕ}
    {d : ((SplitPairCtx × ℕ) × ℕ) × (ℕ × ℕ)} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (h : SplitPairWritePre w d s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (splitPairWriteProg d)) := by
  rcases d with ⟨⟨⟨⟨⟨⟨bL, ⟨qL, vL⟩⟩, ⟨bH, ⟨qH, vH⟩⟩⟩, wv⟩, s_split⟩, idx⟩, qv⟩
  obtain ⟨n_tot, hidx, hv⟩ := h
  have hv' := hv
  obtain ⟨hw, hwv, hqL, hvL, hqH, hvH, _, _, _, _⟩ := hv
  dsimp only [SplitPairCfg.ofCtx] at hwv hqL hvL hqH hvH
  subst hwv
  unfold splitPairWriteProg
  refine validHistory_ite (idx < s_split) ?_ ?_
  · intro _
    exact validHistory_writePairGenProg hwf ⟨hw, rfl, hqL, hvL, valid_lo_frontier hv' hidx⟩
  · intro _
    exact validHistory_writePairGenProg hwf ⟨hw, rfl, hqH, hvH, valid_hi_frontier hv' hidx⟩

/-- Memory history admissibility for `slideUpStepProg`. -/
theorem validHistory_slideUpStepProg {w : ℕ} {d : SplitPairCtx × ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (h : SlideUpStepPre w d s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (slideUpStepProg d)) := by
  rcases d with ⟨⟨⟨⟨bL, ⟨qL, vL⟩⟩, ⟨bH, ⟨qH, vH⟩⟩⟩, wv⟩, s_cur⟩
  obtain ⟨n_tot, hle, hv⟩ := h
  have hv' := hv
  obtain ⟨hw, hwv, hqL, hvL, hqH, hvH, _, hA, _, hfr⟩ := hv
  dsimp only [SplitPairCfg.ofCtx] at hwv hqL hvL hqH hvH hA hfr
  subst hwv
  unfold slideUpStepProg
  refine validHistory_ite (s_cur = 0) ?_ ?_
  · intro _
    have h2 := pairStreamWords_ge_two n_tot qH vH w
    exact validHistory_read_bind (by omega) trivial
  · intro hne
    have hlt : s_cur - 1 < n_tot := by omega
    simp only [pure_bind]
    refine validHistory_bind_wf hwf
      (validHistory_readPairGenProg ⟨hw, rfl, hqL, hvL, valid_lo_frontier hv' hlt⟩)
      fun _ s₁ hwf₁ hf₁ => ?_
    exact validHistory_bind_ro
      (validHistory_writePairGenProg hwf₁
        ⟨hw, rfl, hqH, hvH, lt_of_lt_of_le (valid_hi_frontier hv' hlt) hf₁⟩)
      fun _ _ _ => trivial

/-- Memory history admissibility for `slideUpBatchProg`. -/
theorem validHistory_slideUpBatchProg {w : ℕ} {ctx : SplitPairCtx} {s_split fuel : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (h : SlideUpStepPre w (ctx, s_split) s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (slideUpBatchProg ((ctx, s_split), fuel))) := by
  unfold slideUpBatchProg
  refine validHistory_iterate_inv
    (Inv := fun a' s' => Memory.WellFormed w s' ∧ SlideUpStepPre w (ctx, a') s')
    fuel s_split s ⟨hwf, h⟩
    (fun _ _ ⟨hwf', h'⟩ => validHistory_slideUpStepProg hwf' h') ?_
  intro a' s' ⟨hwf', h'⟩ hv1
  refine ⟨wellFormed_clientState hwf' hv1, ?_⟩
  rcases ctx with ⟨⟨⟨bL, ⟨qL, vL⟩⟩, ⟨bH, ⟨qH, vH⟩⟩⟩, wv⟩
  obtain ⟨n_tot, hle, hval⟩ := h'
  refine ⟨n_tot, ?_, splitPairValid_mono hval (frontier_le_clientState _)⟩
  unfold slideUpStepProg; dsimp only
  by_cases h0 : a' = 0
  · rw [ite_eq_left h0, prog_clientResult_bind, prog_clientResult_pure]; omega
  · rw [ite_eq_right h0]
    simp only [pure_bind, prog_clientResult_bind, prog_clientResult_pure]
    omega

/-- Memory history admissibility for `slideDownStepProg`. -/
theorem validHistory_slideDownStepProg {w : ℕ} {d : (SplitPairCtx × ℕ) × ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (h : SlideDownStepPre w d s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (slideDownStepProg d)) := by
  rcases d with ⟨⟨⟨⟨⟨bL, ⟨qL, vL⟩⟩, ⟨bH, ⟨qH, vH⟩⟩⟩, wv⟩, n_tot⟩, s_cur⟩
  obtain ⟨hle, hv⟩ := h
  have hv' := hv
  obtain ⟨hw, hwv, hqL, hvL, hqH, hvH, _, hA, _, hfr⟩ := hv
  dsimp only [SplitPairCfg.ofCtx] at hwv hqL hvL hqH hvH hA hfr
  subst hwv
  unfold slideDownStepProg
  refine validHistory_ite (s_cur < n_tot) ?_ ?_
  · intro hlt
    refine validHistory_bind_wf hwf
      (validHistory_readPairGenProg ⟨hw, rfl, hqH, hvH, valid_hi_frontier hv' hlt⟩)
      fun _ s₁ hwf₁ hf₁ => ?_
    exact validHistory_bind_ro
      (validHistory_writePairGenProg hwf₁
        ⟨hw, rfl, hqL, hvL, lt_of_lt_of_le (valid_lo_frontier hv' hlt) hf₁⟩)
      fun _ _ _ => trivial
  · intro _
    have h2 := pairStreamWords_ge_two n_tot qH vH w
    exact validHistory_read_bind (by omega) trivial

/-- Memory history admissibility for `slideDownBatchProg`. -/
theorem validHistory_slideDownBatchProg {w : ℕ} {ctx : SplitPairCtx}
    {n_tot s_split fuel : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (h : SlideDownStepPre w ((ctx, n_tot), s_split) s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (slideDownBatchProg (((ctx, n_tot), s_split), fuel))) := by
  unfold slideDownBatchProg
  refine validHistory_iterate_inv
    (Inv := fun a' s' => Memory.WellFormed w s' ∧ SlideDownStepPre w ((ctx, n_tot), a') s')
    fuel s_split s ⟨hwf, h⟩
    (fun _ _ ⟨hwf', h'⟩ => validHistory_slideDownStepProg hwf' h') ?_
  intro a' s' ⟨hwf', h'⟩ hv1
  refine ⟨wellFormed_clientState hwf' hv1, ?_⟩
  rcases ctx with ⟨⟨⟨bL, ⟨qL, vL⟩⟩, ⟨bH, ⟨qH, vH⟩⟩⟩, wv⟩
  obtain ⟨hle, hval⟩ := h'
  refine ⟨?_, splitPairValid_mono hval (frontier_le_clientState _)⟩
  unfold slideDownStepProg; dsimp only
  by_cases hlt : a' < n_tot
  · rw [ite_eq_left hlt]
    simp only [prog_clientResult_bind, prog_clientResult_pure]
    omega
  · rw [ite_eq_right hlt, prog_clientResult_bind, prog_clientResult_pure]
    omega

/-- Memory history admissibility for `zeroWordsStepProg`. -/
theorem validHistory_zeroWordsStepProg {w : ℕ} {d : (ℕ × ℕ) × ℕ} {s : Memory.State}
    (h : ZeroWordsStepPre w d s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (zeroWordsStepProg d)) := by
  rcases d with ⟨⟨base, limit⟩, cur⟩
  obtain ⟨_hw, _hle, hb_lt, hfr⟩ := h
  unfold zeroWordsStepProg
  refine validHistory_ite (cur < limit) ?_ ?_
  · intro hlt
    exact validHistory_write_bind (by omega) (Nat.two_pow_pos w) fun _ _ => trivial
  · intro _
    exact validHistory_read_bind hb_lt trivial

/-- Memory history admissibility for `zeroWordsBatchProg`. -/
theorem validHistory_zeroWordsBatchProg {w base limit cur fuel : ℕ} {s : Memory.State}
    (h : ZeroWordsStepPre w ((base, limit), cur) s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (zeroWordsBatchProg (((base, limit), cur), fuel))) := by
  unfold zeroWordsBatchProg
  refine validHistory_iterate_inv
    (Inv := fun a' s' => ZeroWordsStepPre w ((base, limit), a') s')
    fuel cur s h (fun _ _ h' => validHistory_zeroWordsStepProg h') ?_
  intro a' s' h' _
  obtain ⟨hw, hle, hb_lt, hfr⟩ := h'
  have hfr_le := frontier_le_clientState (zeroWordsStepProg ((base, limit), a')) (s := s')
  refine ⟨hw, ?_, lt_of_lt_of_le hb_lt hfr_le, hfr.trans hfr_le⟩
  unfold zeroWordsStepProg; dsimp only
  by_cases hlt : a' < limit
  · rw [ite_eq_left hlt, prog_clientResult_bind, prog_clientResult_pure]; omega
  · rw [ite_eq_right hlt, prog_clientResult_bind, prog_clientResult_pure]; omega

/-! ## Section 4: `LargePageCoreProg` Programs -/

/-- Memory history admissibility for `pageWriteJobProg`. -/
theorem validHistory_pageWriteJobProg {w mb jk js jc : ℕ} {s : Memory.State}
    (hfr : mb + 32 ≤ s.frontier) (hjk : jk < 2 ^ w) (hjs : js < 2 ^ w) (hjc : jc < 2 ^ w) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pageWriteJobProg (mb, (jk, (js, jc))))) := by
  unfold pageWriteJobProg
  exact validHistory_write_bind (by omega) hjk fun _ h1 =>
    validHistory_write_bind (by omega) hjs fun _ h2 =>
      validHistory_write_only (by omega) hjc

/-- Memory history admissibility for `pageReadFullPagesProg`. -/
theorem validHistory_pageReadFullPagesProg {w mb : ℕ} {s : Memory.State}
    (hfr : mb + 32 ≤ s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pageReadFullPagesProg mb)) := by
  unfold pageReadFullPagesProg
  exact validHistory_read_bind (by omega) (validHistory_read_bind (by omega) trivial)

/-- Memory history admissibility for `pageReadTailCountsProg`. -/
theorem validHistory_pageReadTailCountsProg {w mb : ℕ} {s : Memory.State}
    (hfr : mb + 32 ≤ s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pageReadTailCountsProg mb)) := by
  unfold pageReadTailCountsProg
  exact validHistory_read_bind (by omega) (validHistory_read_bind (by omega) trivial)

/-- Memory history admissibility for `pageReadCleanPosProg`. -/
theorem validHistory_pageReadCleanPosProg {w mb : ℕ} {s : Memory.State}
    (hfr : mb + 32 ≤ s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pageReadCleanPosProg mb)) := by
  unfold pageReadCleanPosProg
  exact validHistory_read_bind (by omega) (validHistory_read_bind (by omega) trivial)

/-- Memory history admissibility for `pageReadJobArgsProg`. -/
theorem validHistory_pageReadJobArgsProg {w mb : ℕ} {s : Memory.State}
    (hfr : mb + 32 ≤ s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pageReadJobArgsProg mb)) := by
  unfold pageReadJobArgsProg
  exact validHistory_read_bind (by omega) (validHistory_read_bind (by omega) trivial)

/-- Memory history admissibility for `pageWriteCleanProg`. -/
theorem validHistory_pageWriteCleanProg {w mb ph cvp coff : ℕ} {s : Memory.State}
    (hfr : mb + 32 ≤ s.frontier) (hph : ph < 2 ^ w) (hcvp : cvp < 2 ^ w) (hcoff : coff < 2 ^ w) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pageWriteCleanProg (mb, (ph, (cvp, coff))))) := by
  unfold pageWriteCleanProg
  exact validHistory_write_bind (by omega) hph fun _ h1 =>
    validHistory_write_bind (by omega) hcvp fun _ h2 =>
      validHistory_write_only (by omega) hcoff

/-- Memory history admissibility for `pageWriteSideMetaProg`. -/
theorem validHistory_pageWriteSideMetaProg {w mb sb qv rv thv : ℕ} {s : Memory.State}
    (hfr : mb + 32 ≤ s.frontier) (hq : qv < 2 ^ w) (hr : rv < 2 ^ w) (hth : thv < 2 ^ w) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pageWriteSideMetaProg ((mb, sb), (qv, (rv, thv))))) := by
  unfold pageWriteSideMetaProg
  exact validHistory_write_bind (by split_ifs <;> omega) hq fun _ h1 =>
    validHistory_write_bind (by split_ifs <;> omega) hr fun _ h2 =>
      validHistory_write_only (by split_ifs <;> omega) hth

private theorem validHistory_readFullPages_bind {α : Type} {w mb : ℕ} {s : Memory.State}
    {q : ℕ × ℕ → Memory.Prog α} (hwf : Memory.WellFormed w s) (hfr : mb + 32 ≤ s.frontier)
    (hq : ∀ fp : ℕ × ℕ, fp.1 < 2 ^ w → fp.2 < 2 ^ w →
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (q fp))) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pageReadFullPagesProg mb >>= q)) := by
  refine validHistory_bind_eq (validHistory_pageReadFullPagesProg hfr) ?_
  have hst : (Memory.spec 0).clientState s (pageReadFullPagesProg mb) = s :=
    runClient_state_pageReadFullPagesProg mb s
  rw [hst]
  exact hq _ (hwf.2 (mb + 21)) (hwf.2 (mb + 22))

private theorem validHistory_readTailCounts_bind {α : Type} {w mb : ℕ} {s : Memory.State}
    {q : ℕ × ℕ → Memory.Prog α} (hwf : Memory.WellFormed w s) (hfr : mb + 32 ≤ s.frontier)
    (hq : ∀ tc : ℕ × ℕ, tc.1 < 2 ^ w → tc.2 < 2 ^ w →
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (q tc))) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pageReadTailCountsProg mb >>= q)) := by
  refine validHistory_bind_eq (validHistory_pageReadTailCountsProg hfr) ?_
  have hst : (Memory.spec 0).clientState s (pageReadTailCountsProg mb) = s :=
    runClient_state_pageReadTailCountsProg mb s
  rw [hst]
  exact hq _ (hwf.2 (mb + 23)) (hwf.2 (mb + 24))

private theorem validHistory_readCleanPos_bind {α : Type} {w mb : ℕ} {s : Memory.State}
    {q : ℕ × ℕ → Memory.Prog α} (hwf : Memory.WellFormed w s) (hfr : mb + 32 ≤ s.frontier)
    (hq : ∀ co : ℕ × ℕ, co.1 < 2 ^ w → co.2 < 2 ^ w →
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (q co))) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pageReadCleanPosProg mb >>= q)) := by
  refine validHistory_bind_eq (validHistory_pageReadCleanPosProg hfr) ?_
  have hst : (Memory.spec 0).clientState s (pageReadCleanPosProg mb) = s :=
    runClient_state_pageReadCleanPosProg mb s
  rw [hst]
  exact hq _ (hwf.2 (mb + 19)) (hwf.2 (mb + 30))

/-- Memory history admissibility for `pageReadPageOfProg`. -/
theorem validHistory_pageReadPageOfProg {w : ℕ} {ctx : PageArenaCtx} {sb vp : ℕ}
    {s : Memory.State} (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pageReadPageOfProg (ctx, (sb, vp)))) := by
  rcases ctx with ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩
  obtain ⟨hw, hwv, hpb, _, _, _, _, _, _, _, _, _, ho2, hm_ib, hib_fr⟩ := hv
  dsimp only [PageArenaLayout.ofCtx] at hwv hpb ho2 hm_ib hib_fr
  subst hwv
  unfold pageReadPageOfProg
  refine validHistory_ite (vp < mp) (fun hvp => ?_) (fun _ => trivial)
  simp only [pure_bind]
  exact validHistory_readPackedCompGen
    ⟨4 * mp, hw, rfl, hpb, by split_ifs <;> omega, by omega⟩

/-- Memory history admissibility for `pageWritePageOfProg`. -/
theorem validHistory_pageWritePageOfProg {w : ℕ} {ctx : PageArenaCtx} {sb vp val : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pageWritePageOfProg ((ctx, (sb, vp)), val))) := by
  rcases ctx with ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩
  obtain ⟨hw, hwv, hpb, _, _, _, _, _, _, _, _, _, ho2, hm_ib, hib_fr⟩ := hv
  dsimp only [PageArenaLayout.ofCtx] at hwv hpb ho2 hm_ib hib_fr
  subst hwv
  unfold pageWritePageOfProg
  refine validHistory_ite (vp < mp) (fun hvp => ?_) (fun _ => trivial)
  simp only [pure_bind]
  exact validHistory_writePackedCompGen hwf
    ⟨4 * mp, hw, rfl, hpb, by split_ifs <;> omega, by omega⟩

/-- Memory history admissibility for `pageReadOwnerProg`. -/
theorem validHistory_pageReadOwnerProg {w : ℕ} {ctx : PageArenaCtx} {P : ℕ}
    {s : Memory.State} (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pageReadOwnerProg (ctx, P))) := by
  rcases ctx with ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩
  obtain ⟨hw, hwv, hpb, _, _, _, _, _, _, _, _, _, ho2, hm_ib, hib_fr⟩ := hv
  dsimp only [PageArenaLayout.ofCtx] at hwv hpb ho2 hm_ib hib_fr
  subst hwv
  unfold pageReadOwnerProg
  refine validHistory_ite (P < mp) (fun hP => ?_) (fun _ => trivial)
  simp only [pure_bind]
  refine validHistory_bind_ro
    (validHistory_readPackedCompGen ⟨4 * mp, hw, rfl, hpb, by omega, by omega⟩)
    fun _ s₁ hf₁ => ?_
  refine validHistory_bind_ro
    (validHistory_readPackedCompGen ⟨4 * mp, hw, rfl, hpb, by omega, by omega⟩)
    fun _ _ _ => trivial

/-- Memory history admissibility for `pageWriteOwnerProg`. -/
theorem validHistory_pageWriteOwnerProg {w : ℕ} {ctx : PageArenaCtx} {P sb vp : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pageWriteOwnerProg ((ctx, P), (sb, vp)))) := by
  rcases ctx with ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩
  obtain ⟨hw, hwv, hpb, _, _, _, _, _, _, _, _, _, ho2, hm_ib, hib_fr⟩ := hv
  dsimp only [PageArenaLayout.ofCtx] at hwv hpb ho2 hm_ib hib_fr
  subst hwv
  unfold pageWriteOwnerProg
  refine validHistory_ite (P < mp) (fun hP => ?_) (fun _ => trivial)
  simp only [pure_bind]
  refine validHistory_bind_wf hwf
    (validHistory_writePackedCompGen hwf ⟨4 * mp, hw, rfl, hpb, by omega, by omega⟩)
    fun _ s₁ hwf₁ hf₁ => ?_
  exact validHistory_writePackedCompGen hwf₁ ⟨4 * mp, hw, rfl, hpb, by omega, by omega⟩

/-- Memory history admissibility for `pageReadTailResProg`. -/
theorem validHistory_pageReadTailResProg {w : ℕ} {ctx : PageArenaCtx} {sb k : ℕ}
    {s : Memory.State} (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pageReadTailResProg (ctx, (sb, k)))) := by
  rcases ctx with ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩
  obtain ⟨hw, hwv, hpb, _, _, _, _, _, _, _, _, _, _, hm_ib, hib_fr⟩ := hv
  dsimp only [PageArenaLayout.ofCtx] at hwv hpb hm_ib hib_fr
  subst hwv
  unfold pageReadTailResProg
  refine validHistory_ite (k < 4 * pg) (fun hk => ?_) (fun _ => trivial)
  simp only [pure_bind]
  exact validHistory_readPackedCompGen
    ⟨16 * pg, hw, rfl, hpb, by split_ifs <;> omega, by omega⟩

/-- Memory history admissibility for `pageWriteTailResProg`. -/
theorem validHistory_pageWriteTailResProg {w : ℕ} {ctx : PageArenaCtx} {sb k val : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pageWriteTailResProg ((ctx, (sb, k)), val))) := by
  rcases ctx with ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩
  obtain ⟨hw, hwv, hpb, _, _, _, _, _, _, _, _, _, _, hm_ib, hib_fr⟩ := hv
  dsimp only [PageArenaLayout.ofCtx] at hwv hpb hm_ib hib_fr
  subst hwv
  unfold pageWriteTailResProg
  refine validHistory_ite (k < 4 * pg) (fun hk => ?_) (fun _ => trivial)
  simp only [pure_bind]
  exact validHistory_writePackedCompGen hwf
    ⟨16 * pg, hw, rfl, hpb, by split_ifs <;> omega, by omega⟩

/-- Memory history admissibility for `pageReadTailOwnerProg`. -/
theorem validHistory_pageReadTailOwnerProg {w : ℕ} {ctx : PageArenaCtx} {res : ℕ}
    {s : Memory.State} (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pageReadTailOwnerProg (ctx, res))) := by
  rcases ctx with ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩
  obtain ⟨hw, hwv, hpb, _, _, _, _, _, _, _, _, _, _, hm_ib, hib_fr⟩ := hv
  dsimp only [PageArenaLayout.ofCtx] at hwv hpb hm_ib hib_fr
  subst hwv
  unfold pageReadTailOwnerProg
  refine validHistory_ite (res < 8 * pg) (fun hres => ?_) (fun _ => trivial)
  simp only [pure_bind]
  exact validHistory_bind_ro
    (validHistory_readPackedCompGen ⟨16 * pg, hw, rfl, hpb, by omega, by omega⟩)
    fun _ _ _ => trivial

/-- Memory history admissibility for `pageWriteTailOwnerProg`. -/
theorem validHistory_pageWriteTailOwnerProg {w : ℕ} {ctx : PageArenaCtx} {res sb k : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pageWriteTailOwnerProg ((ctx, res), (sb, k)))) := by
  rcases ctx with ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩
  obtain ⟨hw, hwv, hpb, _, _, _, _, _, _, _, _, _, _, hm_ib, hib_fr⟩ := hv
  dsimp only [PageArenaLayout.ofCtx] at hwv hpb hm_ib hib_fr
  subst hwv
  unfold pageWriteTailOwnerProg
  refine validHistory_ite (res < 8 * pg ∧ k < 8 * pg) (fun h => ?_) (fun _ => trivial)
  simp only [pure_bind]
  exact validHistory_writePackedCompGen hwf ⟨16 * pg, hw, rfl, hpb, by omega, by omega⟩

/-- Memory history admissibility for `pageSwapPhysProg`. -/
theorem validHistory_pageSwapPhysProg {w : ℕ} {ctx : PageArenaCtx} {p₁ p₂ : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pageSwapPhysProg (ctx, (p₁, p₂)))) := by
  rcases ctx with ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩
  obtain ⟨hw, hwv, _, hqb, hvb, _, _, _, _, _, _, _, _, _, hib_fr⟩ := hv
  dsimp only [PageArenaLayout.ofCtx] at hwv hqb hvb hib_fr
  subst hwv
  unfold pageSwapPhysProg
  refine validHistory_ite (p₁ < nc ∧ p₂ < nc) (fun ⟨hp₁, hp₂⟩ => ?_) (fun _ => trivial)
  have h1 := wOffV_add_one_lt_pairStreamWords (q_bits := qb) (v_bits := vb) hw hp₁
  have h2 := wOffV_add_one_lt_pairStreamWords (q_bits := qb) (v_bits := vb) hw hp₂
  exact validHistory_swapPairGenProg hwf ⟨hw, rfl, hqb, hvb, by omega, by omega⟩

/-- Memory history admissibility for `pageInitScalarsProg`. -/
theorem validHistory_pageInitScalarsProg {w : ℕ} {ctx : PageArenaCtx} {n_0 : ℕ}
    {s : Memory.State} (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pageInitScalarsProg (ctx, n_0))) := by
  have hm32 := pageArenaValid_meta32 hv
  have hpg16 := pageArenaValid_pg16_lt hv
  have hpow0 : 0 < 2 ^ w := Nat.two_pow_pos w
  rcases ctx with ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩
  have hnc_w : nc < 2 ^ w := hv.2.2.2.2.2.2.2.2.2.2.1
  dsimp only [PageArenaLayout.ofCtx] at hm32 hpg16 hnc_w
  unfold pageInitScalarsProg
  refine validHistory_ite (n_0 ≤ nc) (fun hn0 => ?_) (fun _ => trivial)
  simp only [pure_bind]
  have hq0_lt : (if n_0 < pg + (pg + pg / 2) then 0
      else (n_0 - (pg + pg / 2)) / pg) < 2 ^ w := by
    have hdiv : (n_0 - (pg + pg / 2)) / pg ≤ n_0 - (pg + pg / 2) := Nat.div_le_self _ pg
    split_ifs <;> omega
  have hr0_lt : n_0 - (if n_0 < pg + (pg + pg / 2) then 0
      else (n_0 - (pg + pg / 2)) / pg) * pg < 2 ^ w := by omega
  exact validHistory_write_bind (by omega) hpow0 fun _ h1 =>
    validHistory_write_bind (by omega) hpow0 fun _ h2 =>
      validHistory_write_bind (by omega) (by omega) fun _ h3 =>
        validHistory_write_bind (by omega) hq0_lt fun _ h4 =>
          validHistory_write_bind (by omega) hpow0 fun _ h5 =>
            validHistory_write_bind (by omega) hr0_lt fun _ h6 =>
              validHistory_write_bind (by omega) hpow0 fun _ h7 =>
                validHistory_write_bind (by omega) hpow0 fun _ h8 =>
                  validHistory_write_bind (by omega) hpow0 fun _ h9 =>
                    validHistory_bind_ro
                      (validHistory_pageWriteJobProg (by omega) hpow0 hpow0 hpow0)
                      fun _ _ h10 =>
                        validHistory_write_bind (by omega) hpow0 fun _ h11 =>
                          validHistory_write_only (by omega) hpow0

/-- Memory history admissibility for `pageInitDirStepProg`. -/
theorem validHistory_pageInitDirStepProg {w : ℕ} {ctx : PageArenaCtx} {cur : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pageInitDirStepProg (ctx, cur))) := by
  rcases ctx with ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩
  unfold pageInitDirStepProg
  refine validHistory_ite (cur < mp) ?_ ?_
  · intro _
    simp only [pure_bind]
    refine validHistory_bind_page hwf hv (validHistory_pageWritePageOfProg hwf hv)
      fun _ _ hwf1 hv1 => ?_
    refine validHistory_bind_page hwf1 hv1 (validHistory_pageWritePageOfProg hwf1 hv1)
      fun _ _ hwf2 hv2 => ?_
    refine validHistory_bind_page hwf2 hv2 (validHistory_pageWriteOwnerProg hwf2 hv2)
      fun _ _ _ hv3 => ?_
    have hm32 := pageArenaValid_meta32 hv3
    dsimp only [PageArenaLayout.ofCtx] at hm32
    exact validHistory_read_bind (by omega) trivial
  · intro _
    have hm32 := pageArenaValid_meta32 hv
    dsimp only [PageArenaLayout.ofCtx] at hm32
    exact validHistory_read_bind (by omega) trivial

/-- Memory history admissibility for `pageInitDirBatchProg`. -/
theorem validHistory_pageInitDirBatchProg {w : ℕ} {ctx : PageArenaCtx} {cur fuel : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pageInitDirBatchProg ((ctx, cur), fuel))) := by
  unfold pageInitDirBatchProg
  exact validHistory_iterate_wf fuel cur s hwf hv
    (fun _ _ hle h => pageArenaValid_mono h hle)
    (fun _ _ hwf' hv' => validHistory_pageInitDirStepProg hwf' hv')

private theorem validHistory_pageInitTailResSubProg {w : ℕ} {ctx : PageArenaCtx}
    {qb_mod cur : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pageInitTailResSubProg ((ctx, qb_mod), cur))) := by
  rcases ctx with ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩
  unfold pageInitTailResSubProg
  refine validHistory_ite (cur < 4 * pg) (fun _ => ?_) (fun _ => trivial)
  simp only [pure_bind]
  exact validHistory_bind_page hwf hv (validHistory_pageWriteTailResProg hwf hv)
    fun _ _ hwf1 hv1 => validHistory_pageWriteTailResProg hwf1 hv1

/-- Memory history admissibility for `pageInitTailStepProg`. -/
theorem validHistory_pageInitTailStepProg {w : ℕ} {ctx : PageArenaCtx} {n_0 cur : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pageInitTailStepProg ((ctx, n_0), cur))) := by
  rcases ctx with ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩
  unfold pageInitTailStepProg
  refine validHistory_ite (n_0 ≤ nc ∧ cur < 8 * pg) ?_ ?_
  · intro _
    simp only [pure_bind]
    refine validHistory_bind_page hwf hv (validHistory_pageInitTailResSubProg hwf hv)
      fun _ _ hwf1 hv1 => ?_
    refine validHistory_bind_page hwf1 hv1 (validHistory_pageWriteTailOwnerProg hwf1 hv1)
      fun _ _ _ hv2 => ?_
    have hm32 := pageArenaValid_meta32 hv2
    dsimp only [PageArenaLayout.ofCtx] at hm32
    exact validHistory_read_bind (by omega) trivial
  · intro _
    have hm32 := pageArenaValid_meta32 hv
    dsimp only [PageArenaLayout.ofCtx] at hm32
    exact validHistory_read_bind (by omega) trivial

/-- Memory history admissibility for `pageInitTailBatchProg`. -/
theorem validHistory_pageInitTailBatchProg {w : ℕ} {ctx : PageArenaCtx} {n_0 cur fuel : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pageInitTailBatchProg (((ctx, n_0), cur), fuel))) := by
  unfold pageInitTailBatchProg
  exact validHistory_iterate_wf fuel cur s hwf hv
    (fun _ _ hle h => pageArenaValid_mono h hle)
    (fun _ _ hwf' hv' => validHistory_pageInitTailStepProg hwf' hv')

private theorem validHistory_pageTailPhysInnerProg {w : ℕ} {ctx : PageArenaCtx}
    {sb k base tsum : ℕ} {s : Memory.State}
    (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s
        (pageTailPhysInnerProg ((ctx, (sb, k)), (base, tsum)))) := by
  rcases ctx with ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩
  unfold pageTailPhysInnerProg
  refine validHistory_bind_ro (validHistory_pageReadTailResProg hv) fun _ _ _ => ?_
  refine validHistory_ite _ (fun _ => ?_) (fun _ => trivial)
  simp only [pure_bind]
  exact validHistory_ite _ (fun _ => trivial) (fun _ => trivial)

private theorem validHistory_pageTailPhysDispatchProg {w : ℕ} {ctx : PageArenaCtx}
    {sb t base : ℕ} {tc : ℕ × ℕ} {th : ℕ} {s : Memory.State}
    (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s
        (pageTailPhysDispatchProg (((ctx, (sb, t)), base), (tc, th)))) := by
  rcases ctx with ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩
  unfold pageTailPhysDispatchProg
  refine validHistory_ite _ (fun _ => ?_) (fun _ => trivial)
  refine validHistory_ite _ (fun _ => ?_) (fun _ => trivial)
  simp only [pure_bind]
  exact validHistory_pageTailPhysInnerProg hv

/-- Memory history admissibility for `pageTailPhysBoundedProg`. -/
theorem validHistory_pageTailPhysBoundedProg {w : ℕ} {ctx : PageArenaCtx} {sb t : ℕ}
    {s : Memory.State} (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pageTailPhysBoundedProg (ctx, (sb, t)))) := by
  have hm32 := pageArenaValid_meta32 hv
  rcases ctx with ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩
  dsimp only [PageArenaLayout.ofCtx] at hm32
  unfold pageTailPhysBoundedProg
  refine validHistory_bind_page_ro hv (validHistory_pageReadFullPagesProg hm32) fun _ _ hv1 => ?_
  have hm1 := pageArenaValid_meta32 hv1
  dsimp only [PageArenaLayout.ofCtx] at hm1
  refine validHistory_bind_page_ro hv1 (validHistory_pageReadTailCountsProg hm1) fun _ _ hv2 => ?_
  have hm2 := pageArenaValid_meta32 hv2
  dsimp only [PageArenaLayout.ofCtx] at hm2
  refine validHistory_read_bind (by split_ifs <;> omega) ?_
  refine validHistory_ite _ (fun _ => ?_) (fun _ => trivial)
  refine validHistory_ite _ (fun _ => ?_) (fun _ => trivial)
  simp only [pure_bind]
  exact validHistory_pageTailPhysDispatchProg hv2

private theorem validHistory_pageEffDemoteInnerProg {w : ℕ} {ctx : PageArenaCtx}
    {sb qm1 pRaw pLast : ℕ} {s : Memory.State}
    (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s
        (pageEffDemoteInnerProg (ctx, ((sb, qm1), (pRaw, pLast))))) := by
  unfold pageEffDemoteInnerProg
  exact validHistory_bind_ro (validHistory_pageReadPageOfProg hv) fun _ _ _ => trivial

private theorem validHistory_pageEffDemoteCheckProg {w : ℕ} {ctx : PageArenaCtx}
    {pRaw u_off jk : ℕ} {ja fp : ℕ × ℕ} {s : Memory.State}
    (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s
        (pageEffDemoteCheckProg ((ctx, (pRaw, u_off)), ((jk, ja), fp)))) := by
  unfold pageEffDemoteCheckProg
  simp only [pure_bind]
  refine validHistory_ite _ (fun _ => ?_) (fun _ => trivial)
  exact validHistory_pageEffDemoteInnerProg hv

private theorem validHistory_pageEffDemoteBoundedProg {w : ℕ} {ctx : PageArenaCtx}
    {pRaw u_off : ℕ} {s : Memory.State}
    (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pageEffDemoteBoundedProg (ctx, (pRaw, u_off)))) := by
  have hm32 := pageArenaValid_meta32 hv
  rcases ctx with ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩
  dsimp only [PageArenaLayout.ofCtx] at hm32
  unfold pageEffDemoteBoundedProg
  refine validHistory_read_bind (by omega) ?_
  refine validHistory_bind_page_ro hv (validHistory_pageReadJobArgsProg hm32) fun _ _ hv1 => ?_
  have hm1 := pageArenaValid_meta32 hv1
  dsimp only [PageArenaLayout.ofCtx] at hm1
  refine validHistory_bind_page_ro hv1 (validHistory_pageReadFullPagesProg hm1) fun _ _ hv2 => ?_
  refine validHistory_ite _ (fun _ => ?_) (fun _ => trivial)
  refine validHistory_ite _ (fun _ => ?_) (fun _ => trivial)
  exact validHistory_pageEffDemoteCheckProg hv2

private theorem validHistory_pageEffPageBoundedProg {w : ℕ} {ctx : PageArenaCtx}
    {pRaw u_off : ℕ} {s : Memory.State}
    (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pageEffPageBoundedProg (ctx, (pRaw, u_off)))) := by
  have hm32 := pageArenaValid_meta32 hv
  rcases ctx with ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩
  dsimp only [PageArenaLayout.ofCtx] at hm32
  unfold pageEffPageBoundedProg
  refine validHistory_read_bind (by omega) ?_
  refine validHistory_bind_page_ro hv (validHistory_pageReadCleanPosProg hm32) fun _ _ hv1 => ?_
  refine validHistory_ite _ (fun _ => ?_) (fun _ => validHistory_pageEffDemoteBoundedProg hv1)
  refine validHistory_ite _ (fun _ => ?_) (fun _ => trivial)
  simp only [pure_bind]
  exact validHistory_bind_ro (validHistory_pageReadPageOfProg hv1) fun _ _ _ => trivial

private theorem validHistory_pageFullPhysBoundedProg {w : ℕ} {ctx : PageArenaCtx}
    {sb idx Q : ℕ} {s : Memory.State}
    (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pageFullPhysBoundedProg (ctx, ((sb, idx), Q)))) := by
  rcases ctx with ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩
  unfold pageFullPhysBoundedProg
  simp only [pure_bind]
  refine validHistory_bind_page_ro hv (validHistory_pageReadPageOfProg hv) fun _ _ hv1 => ?_
  refine validHistory_bind_ro (validHistory_pageEffPageBoundedProg hv1) fun _ _ _ => ?_
  exact validHistory_ite _ (fun _ => trivial) (fun _ => trivial)

/-- Memory history admissibility for `pageToPhysBoundedProg`. -/
theorem validHistory_pageToPhysBoundedProg {w : ℕ} {ctx : PageArenaCtx} {sb idx : ℕ}
    {s : Memory.State} (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pageToPhysBoundedProg (ctx, (sb, idx)))) := by
  have hm32 := pageArenaValid_meta32 hv
  rcases ctx with ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩
  dsimp only [PageArenaLayout.ofCtx] at hm32
  unfold pageToPhysBoundedProg
  refine validHistory_bind_page_ro hv (validHistory_pageReadFullPagesProg hm32) fun _ _ hv1 => ?_
  refine validHistory_ite _ (fun _ => ?_) (fun _ => trivial)
  refine validHistory_ite _ (fun _ => ?_) (fun _ => trivial)
  simp only [pure_bind]
  refine validHistory_ite _ (fun _ => ?_) (fun _ => ?_)
  · exact validHistory_pageFullPhysBoundedProg hv1
  · exact validHistory_pageTailPhysBoundedProg hv1

/-- Memory history admissibility for `pageReadVirtBoundedProg`. -/
theorem validHistory_pageReadVirtBoundedProg {w : ℕ} {ctx : PageArenaCtx} {sb idx : ℕ}
    {s : Memory.State} (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pageReadVirtBoundedProg (ctx, (sb, idx)))) := by
  rcases ctx with ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩
  unfold pageReadVirtBoundedProg
  refine validHistory_bind_page_ro hv (validHistory_pageToPhysBoundedProg hv) fun p _ hv1 => ?_
  refine validHistory_ite (p < nc) (fun hp => ?_) (fun _ => trivial)
  obtain ⟨hw, hwv, _, hqb, hvb, _, _, _, _, _, _, _, _, _, hib_fr⟩ := hv1
  dsimp only [PageArenaLayout.ofCtx] at hwv hqb hvb hib_fr
  subst hwv
  have hlt := wOffV_add_one_lt_pairStreamWords (q_bits := qb) (v_bits := vb) hw hp
  exact validHistory_readPairGenProg ⟨hw, rfl, hqb, hvb, by omega⟩

/-- Memory history admissibility for `pageWriteVirtBoundedProg`. -/
theorem validHistory_pageWriteVirtBoundedProg {w : ℕ} {ctx : PageArenaCtx} {sb idx : ℕ}
    {qv : ℕ × ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pageWriteVirtBoundedProg ((ctx, (sb, idx)), qv))) := by
  rcases ctx with ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩
  unfold pageWriteVirtBoundedProg
  refine validHistory_bind_page hwf hv (validHistory_pageToPhysBoundedProg hv)
    fun p _ hwf1 hv1 => ?_
  refine validHistory_ite (p < nc) (fun hp => ?_) (fun _ => trivial)
  obtain ⟨hw, hwv, _, hqb, hvb, _, _, _, _, _, _, _, _, _, hib_fr⟩ := hv1
  dsimp only [PageArenaLayout.ofCtx] at hwv hqb hvb hib_fr
  subst hwv
  have hlt := wOffV_add_one_lt_pairStreamWords (q_bits := qb) (v_bits := vb) hw hp
  exact validHistory_writePairGenProg hwf1 ⟨hw, rfl, hqb, hvb, by omega⟩

/-- Memory history admissibility for `pageSwapTailSlotsProg`. -/
theorem validHistory_pageSwapTailSlotsProg {w : ℕ} {ctx : PageArenaCtx} {p₁ p₂ : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pageSwapTailSlotsProg (ctx, (p₁, p₂)))) := by
  rcases ctx with ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩
  unfold pageSwapTailSlotsProg
  refine validHistory_ite (p₁ = p₂) (fun _ => trivial) (fun _ => ?_)
  refine validHistory_ite (p₁ < nc ∧ p₂ < nc) (fun _ => ?_) (fun _ => trivial)
  simp only [pure_bind]
  refine validHistory_bind_page hwf hv (validHistory_pageReadTailOwnerProg hv)
    fun _ _ hwf1 hv1 => ?_
  refine validHistory_bind_page hwf1 hv1 (validHistory_pageReadTailOwnerProg hv1)
    fun _ _ hwf2 hv2 => ?_
  refine validHistory_bind_page hwf2 hv2 (validHistory_pageWriteTailResProg hwf2 hv2)
    fun _ _ hwf3 hv3 => ?_
  refine validHistory_bind_page hwf3 hv3 (validHistory_pageWriteTailResProg hwf3 hv3)
    fun _ _ hwf4 hv4 => ?_
  refine validHistory_bind_page hwf4 hv4 (validHistory_pageWriteTailOwnerProg hwf4 hv4)
    fun _ _ hwf5 hv5 => ?_
  refine validHistory_bind_page hwf5 hv5 (validHistory_pageWriteTailOwnerProg hwf5 hv5)
    fun _ _ hwf6 hv6 => ?_
  exact validHistory_pageSwapPhysProg hwf6 hv6

private theorem validHistory_pageStartDemoteCheckProg {w : ℕ} {ctx : PageArenaCtx}
    {sb qs Q : ℕ} {s : Memory.State}
    (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pageStartDemoteCheckProg (ctx, ((sb, qs), Q)))) := by
  unfold pageStartDemoteCheckProg
  simp only [pure_bind]
  refine validHistory_bind_ro (validHistory_pageReadPageOfProg hv) fun _ _ _ => ?_
  exact validHistory_ite _ (fun _ => trivial) (fun _ => trivial)

private theorem validHistory_pageStartSideCheckProg {w : ℕ} {ctx : PageArenaCtx}
    {sb q0 q1 r : ℕ} {s : Memory.State}
    (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s
        (pageStartSideCheckProg ((ctx, sb), ((q0, q1), r)))) := by
  rcases ctx with ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩
  unfold pageStartSideCheckProg
  simp only [pure_bind]
  refine validHistory_ite _ (fun _ => trivial) (fun _ => ?_)
  refine validHistory_ite _ (fun _ => ?_) (fun _ => trivial)
  exact validHistory_pageStartDemoteCheckProg hv

private theorem validHistory_pageStartSideProg {w : ℕ} {ctx : PageArenaCtx} {sb : ℕ}
    {s : Memory.State} (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pageStartSideProg (ctx, sb))) := by
  have hm32 := pageArenaValid_meta32 hv
  rcases ctx with ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩
  dsimp only [PageArenaLayout.ofCtx] at hm32
  unfold pageStartSideProg
  refine validHistory_read_bind (by omega) ?_
  refine validHistory_read_bind (by omega) ?_
  refine validHistory_read_bind (by split_ifs <;> omega) ?_
  refine validHistory_ite _ (fun _ => ?_) (fun _ => trivial)
  exact validHistory_pageStartSideCheckProg hv

private theorem pageStartSideProg_job_bounds (ctx : PageArenaCtx) (sb : ℕ) (s : Memory.State) :
    let r := (Memory.spec 0).clientResult s (pageStartSideProg (ctx, sb))
    r.2.1 ≤ 3 ∧ r.2.2.1 ≤ 1 ∧ r.2.2.2 = 0 := by
  have hdem : ∀ sb' qs Q s', sb' ≤ 1 →
      let r := (Memory.spec 0).clientResult s' (pageStartDemoteCheckProg (ctx, ((sb', qs), Q)))
      r.2.1 ≤ 3 ∧ r.2.2.1 ≤ 1 ∧ r.2.2.2 = 0 := by
    intro sb' qs Q s' hsb
    unfold pageStartDemoteCheckProg
    simp only [pure_bind, prog_clientResult_bind]
    split_ifs
    · exact ⟨le_rfl, hsb, rfl⟩
    · exact ⟨Nat.le_succ 2, hsb, rfl⟩
  have hchk : ∀ q0 q1 rv s',
      let r := (Memory.spec 0).clientResult s'
        (pageStartSideCheckProg ((ctx, sb), ((q0, q1), rv)))
      r.2.1 ≤ 3 ∧ r.2.2.1 ≤ 1 ∧ r.2.2.2 = 0 := by
    intro q0 q1 rv s'
    rcases ctx with ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩
    unfold pageStartSideCheckProg
    simp only [pure_bind]
    have hsb_le : (if sb = 0 then 0 else 1) ≤ 1 := by split_ifs <;> omega
    by_cases h1 : 11 * pg ≤ 4 * rv
    · rw [ite_eq_left h1, prog_clientResult_pure]
      exact ⟨Nat.succ_le_succ (Nat.zero_le 2), hsb_le, rfl⟩
    · rw [ite_eq_right h1]
      by_cases h2 : 0 < (if sb = 0 then q0 else q1) ∧ 4 * rv ≤ 5 * pg
      · rw [ite_eq_left h2]; exact hdem _ _ _ s' hsb_le
      · rw [ite_eq_right h2, prog_clientResult_pure]; exact ⟨Nat.zero_le 3, Nat.zero_le 1, rfl⟩
  rcases ctx with ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩
  unfold pageStartSideProg
  dsimp only
  rw [prog_clientResult_bind, prog_clientResult_bind, prog_clientResult_bind]
  split_ifs <;> first | exact hchk _ _ _ _ | exact ⟨Nat.zero_le 3, Nat.zero_le 1, rfl⟩

/-- Memory history admissibility for `pageMaybeStartJobProg`. -/
theorem validHistory_pageMaybeStartJobProg {w : ℕ} {ctx : PageArenaCtx} {s : Memory.State}
    (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pageMaybeStartJobProg ctx)) := by
  have hm32 := pageArenaValid_meta32 hv
  have hw32 := pageArenaValid_const_lt hv
  rcases ctx with ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩
  dsimp only [PageArenaLayout.ofCtx] at hm32
  unfold pageMaybeStartJobProg
  refine validHistory_read_bind (by omega) ?_
  refine validHistory_ite _ (fun _ => ?_) (fun _ => trivial)
  simp only [pure_bind]
  refine validHistory_bind_eq (validHistory_pageStartSideProg hv) ?_
  have hst0 := runClient_state_pageStartSideProg
    (((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)), 0) s
  rw [show (Memory.spec 0).clientState s
      (pageStartSideProg
        ((((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)), 0))) = s from hst0]
  obtain ⟨hjk0, hjs0, hjc0⟩ := pageStartSideProg_job_bounds
    ((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)) 0 s
  refine validHistory_ite _ (fun _ => ?_) (fun _ => ?_)
  · exact validHistory_pageWriteJobProg hm32
      (lt_of_le_of_lt hjk0 (by omega)) (lt_of_le_of_lt hjs0 (by omega))
      (by rw [hjc0]; exact Nat.two_pow_pos w)
  · refine validHistory_bind_eq (validHistory_pageStartSideProg hv) ?_
    have hst1 := runClient_state_pageStartSideProg
      (((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)), 1) s
    rw [show (Memory.spec 0).clientState s
        (pageStartSideProg
          ((((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)), 1))) = s from hst1]
    obtain ⟨hjk1, hjs1, hjc1⟩ := pageStartSideProg_job_bounds
      ((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)) 1 s
    refine validHistory_ite _ (fun _ => ?_) (fun _ => trivial)
    exact validHistory_pageWriteJobProg hm32
      (lt_of_le_of_lt hjk1 (by omega)) (lt_of_le_of_lt hjs1 (by omega))
      (by rw [hjc1]; exact Nat.two_pow_pos w)

private theorem validHistory_pageCommitPromoteDirProg {w : ℕ} {ctx : PageArenaCtx}
    {sb qs Q : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pageCommitPromoteDirProg (ctx, (sb, (qs, Q))))) := by
  rcases ctx with ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩
  unfold pageCommitPromoteDirProg
  simp only [pure_bind]
  refine validHistory_bind_page hwf hv (validHistory_pageWritePageOfProg hwf hv)
    fun _ _ hwf1 hv1 => ?_
  refine validHistory_bind_page hwf1 hv1 (validHistory_pageWriteOwnerProg hwf1 hv1)
    fun _ _ _ hv2 => ?_
  have hm32 := pageArenaValid_meta32 hv2
  dsimp only [PageArenaLayout.ofCtx] at hm32
  have hpow0 : 0 < 2 ^ w := Nat.two_pow_pos w
  exact validHistory_pageWriteJobProg hm32 hpow0 hpow0 hpow0

private theorem validHistory_pageTickPromoteEndProg {w : ℕ} {ctx : PageArenaCtx}
    {sb qs Q : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pageTickPromoteEndProg (ctx, (sb, (qs, Q))))) := by
  have hm32 := pageArenaValid_meta32 hv
  have hpg16 := pageArenaValid_pg16_lt hv
  have hmp4 := pageArenaValid_mp4_lt hv
  rcases ctx with ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩
  have hpg32 : 32 ≤ pg := hv.2.2.2.2.2.1
  dsimp only [PageArenaLayout.ofCtx] at hm32 hpg16 hmp4
  unfold pageTickPromoteEndProg
  refine validHistory_readTailCounts_bind hwf hm32 fun tc htc1 htc2 => ?_
  simp only [pure_bind]
  refine validHistory_read_bind (by split_ifs <;> omega) ?_
  refine validHistory_ite _ (fun hgd => ?_) (fun _ => trivial)
  obtain ⟨hqs, _, _, _⟩ := hgd
  have hmod : (s.mem (mb + if sb = 0 then 25 else 26) + pg) % (4 * pg) < 4 * pg :=
    Nat.mod_lt _ (by omega)
  have hrv : (if sb = 0 then tc.1 else tc.2) - pg < 2 ^ w := by
    split_ifs <;> omega
  refine validHistory_bind_page hwf hv
    (validHistory_pageWriteSideMetaProg hm32 (by omega) hrv (by omega))
    fun _ _ hwf1 hv1 => validHistory_pageCommitPromoteDirProg hwf1 hv1

private theorem validHistory_pageTickPromoteStepProg {w : ℕ} {ctx : PageArenaCtx}
    {sb cur Q : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier)
    (hsb : sb < 2 ^ w) (hcur : cur + 1 < 2 ^ w) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pageTickPromoteStepProg (ctx, ((sb, cur), Q)))) := by
  have hw32 := pageArenaValid_const_lt hv
  rcases ctx with ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩
  unfold pageTickPromoteStepProg
  refine validHistory_bind_page hwf hv (validHistory_pageTailPhysBoundedProg hv)
    fun _ _ hwf1 hv1 => ?_
  refine validHistory_ite _ (fun _ => ?_) (fun _ => trivial)
  simp only [pure_bind]
  refine validHistory_bind_page hwf1 hv1 (validHistory_pageSwapTailSlotsProg hwf1 hv1)
    fun _ _ _ hv2 => ?_
  have hm32 := pageArenaValid_meta32 hv2
  dsimp only [PageArenaLayout.ofCtx] at hm32
  exact validHistory_pageWriteJobProg hm32 (by omega) hsb hcur

private theorem validHistory_pageTickPromoteProg {w : ℕ} {ctx : PageArenaCtx} {js cur : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pageTickPromoteProg (ctx, (js, cur)))) := by
  have hm32 := pageArenaValid_meta32 hv
  have hpg16 := pageArenaValid_pg16_lt hv
  have hw32 := pageArenaValid_const_lt hv
  rcases ctx with ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩
  dsimp only [PageArenaLayout.ofCtx] at hm32 hpg16
  unfold pageTickPromoteProg
  refine validHistory_bind_page hwf hv (validHistory_pageReadFullPagesProg hm32)
    fun _ _ hwf1 hv1 => ?_
  simp only [pure_bind]
  refine validHistory_ite _ (fun _ => ?_) (fun _ => trivial)
  refine validHistory_ite _ (fun _ => ?_) (fun _ => trivial)
  refine validHistory_ite (cur < pg) ?_ ?_
  · intro hcur
    have hsb : (if js = 0 then 0 else 1) < 2 ^ w := by split_ifs <;> omega
    exact validHistory_pageTickPromoteStepProg hwf1 hv1 hsb (by omega)
  · intro _
    exact validHistory_pageTickPromoteEndProg hwf1 hv1

private theorem validHistory_pageSwapDemoteDirProg {w : ℕ} {ctx : PageArenaCtx}
    {sb qm1 pDem pLast : ℕ} {owLast : ℕ × ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s
        (pageSwapDemoteDirProg (ctx, ((sb, qm1), ((pDem, pLast), owLast))))) := by
  rcases owLast with ⟨os, ov⟩
  unfold pageSwapDemoteDirProg
  refine validHistory_bind_page hwf hv (validHistory_pageWritePageOfProg hwf hv)
    fun _ _ hwf1 hv1 => ?_
  refine validHistory_bind_page hwf1 hv1 (validHistory_pageWritePageOfProg hwf1 hv1)
    fun _ _ hwf2 hv2 => ?_
  refine validHistory_bind_page hwf2 hv2 (validHistory_pageWriteOwnerProg hwf2 hv2)
    fun _ _ hwf3 hv3 => validHistory_pageWriteOwnerProg hwf3 hv3

private theorem validHistory_pageTickDemoteSwapBodyProg {w : ℕ} {ctx : PageArenaCtx}
    {sb qm1 pDem pLast cur : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier) (hsb : sb < 2 ^ w) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s
        (pageTickDemoteSwapBodyProg (ctx, ((sb, qm1), ((pDem, pLast), cur))))) := by
  have hpg16 := pageArenaValid_pg16_lt hv
  have hw32 := pageArenaValid_const_lt hv
  rcases ctx with ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩
  dsimp only [PageArenaLayout.ofCtx] at hpg16
  unfold pageTickDemoteSwapBodyProg
  refine validHistory_ite (cur < pg) ?_ ?_
  · intro hcur
    simp only [pure_bind]
    refine validHistory_bind_page hwf hv (validHistory_pageSwapPhysProg hwf hv)
      fun _ _ _ hv1 => ?_
    have hm32 := pageArenaValid_meta32 hv1
    dsimp only [PageArenaLayout.ofCtx] at hm32
    exact validHistory_pageWriteJobProg hm32 (by omega) hsb (by omega)
  · intro _
    refine validHistory_bind_page hwf hv (validHistory_pageReadOwnerProg hv)
      fun _ _ hwf1 hv1 => ?_
    simp only [pure_bind]
    refine validHistory_bind_page hwf1 hv1 (validHistory_pageSwapDemoteDirProg hwf1 hv1)
      fun _ _ _ hv2 => ?_
    have hm32 := pageArenaValid_meta32 hv2
    dsimp only [PageArenaLayout.ofCtx] at hm32
    exact validHistory_pageWriteJobProg hm32 (by omega) hsb (Nat.two_pow_pos w)

private theorem validHistory_pageTickDemoteSwapCheckProg {w : ℕ} {ctx : PageArenaCtx}
    {sb cur : ℕ} {fp : ℕ × ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier) (hsb : sb < 2 ^ w) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pageTickDemoteSwapCheckProg ((ctx, (sb, cur)), fp))) := by
  rcases ctx with ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩
  unfold pageTickDemoteSwapCheckProg
  simp only [pure_bind]
  refine validHistory_ite _ (fun _ => ?_) (fun _ => trivial)
  refine validHistory_bind_page hwf hv (validHistory_pageReadPageOfProg hv)
    fun _ _ hwf1 hv1 => ?_
  refine validHistory_ite _ (fun _ => ?_) (fun _ => trivial)
  exact validHistory_pageTickDemoteSwapBodyProg hwf1 hv1 hsb

private theorem validHistory_pageTickDemoteSwapProg {w : ℕ} {ctx : PageArenaCtx} {js cur : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pageTickDemoteSwapProg (ctx, (js, cur)))) := by
  have hm32 := pageArenaValid_meta32 hv
  have hw32 := pageArenaValid_const_lt hv
  rcases ctx with ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩
  dsimp only [PageArenaLayout.ofCtx] at hm32
  unfold pageTickDemoteSwapProg
  refine validHistory_bind_page hwf hv (validHistory_pageReadFullPagesProg hm32)
    fun _ _ hwf1 hv1 => ?_
  simp only [pure_bind]
  refine validHistory_ite _ (fun _ => ?_) (fun _ => trivial)
  refine validHistory_ite _ (fun _ => ?_) (fun _ => trivial)
  have hsb : (if js = 0 then 0 else 1) < 2 ^ w := by split_ifs <;> omega
  exact validHistory_pageTickDemoteSwapCheckProg hwf1 hv1 hsb

private theorem validHistory_pageTickDemoteBuildStepProg {w : ℕ} {ctx : PageArenaCtx}
    {sb cur ths Q : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier)
    (hsb : sb < 2 ^ w) (hcur : cur + 1 < 2 ^ w) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s
        (pageTickDemoteBuildStepProg (ctx, ((sb, cur), (ths, Q))))) := by
  have hw32 := pageArenaValid_const_lt hv
  rcases ctx with ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩
  unfold pageTickDemoteBuildStepProg
  simp only [pure_bind]
  refine validHistory_bind_page hwf hv (validHistory_pageWriteTailResProg hwf hv)
    fun _ _ hwf1 hv1 => ?_
  refine validHistory_bind_page hwf1 hv1 (validHistory_pageWriteTailOwnerProg hwf1 hv1)
    fun _ _ _ hv2 => ?_
  have hm32 := pageArenaValid_meta32 hv2
  dsimp only [PageArenaLayout.ofCtx] at hm32
  exact validHistory_pageWriteJobProg hm32 (by omega) hsb hcur

private theorem validHistory_pageTickDemoteBuildEndProg {w mb pg sb qs rs ths : ℕ}
    {s : Memory.State} (hfr : mb + 32 ≤ s.frontier) (hpg : 0 < pg) (hpg16 : 16 * pg < 2 ^ w)
    (hqs : qs < 2 ^ w) (hrs : rs < 3 * pg) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s
        (pageTickDemoteBuildEndProg ((mb, pg), ((sb, qs), (rs, ths))))) := by
  unfold pageTickDemoteBuildEndProg
  simp only [pure_bind]
  have hmod : (ths + 3 * pg) % (4 * pg) < 4 * pg := Nat.mod_lt _ (by omega)
  refine validHistory_bind_ro
    (validHistory_pageWriteSideMetaProg hfr (by omega) (by omega) (by omega))
    fun _ _ hf1 => ?_
  have hpow0 : 0 < 2 ^ w := Nat.two_pow_pos w
  exact validHistory_pageWriteJobProg (hfr.trans hf1) hpow0 hpow0 hpow0

private theorem validHistory_pageTickDemoteBuildCheckProg {w : ℕ} {ctx : PageArenaCtx}
    {sb cur : ℕ} {fp tc : ℕ × ℕ} {ths : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier)
    (hsb : sb < 2 ^ w) (hfp1 : fp.1 < 2 ^ w) (hfp2 : fp.2 < 2 ^ w) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s
        (pageTickDemoteBuildCheckProg ((ctx, (sb, cur)), (fp, (tc, ths))))) := by
  have hm32 := pageArenaValid_meta32 hv
  have hpg16 := pageArenaValid_pg16_lt hv
  rcases ctx with ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩
  have hpg32 : 32 ≤ pg := hv.2.2.2.2.2.1
  dsimp only [PageArenaLayout.ofCtx] at hm32 hpg16
  unfold pageTickDemoteBuildCheckProg
  simp only [pure_bind]
  refine validHistory_ite _ (fun hgd => ?_) (fun _ => trivial)
  obtain ⟨_, _, hrs, _⟩ := hgd
  refine validHistory_ite (cur < pg) ?_ ?_
  · intro hcur
    exact validHistory_pageTickDemoteBuildStepProg hwf hv hsb (by omega)
  · intro _
    have hqs : (if sb = 0 then fp.1 else fp.2) < 2 ^ w := by split_ifs <;> assumption
    exact validHistory_pageTickDemoteBuildEndProg hm32 (by omega) hpg16 hqs hrs

private theorem validHistory_pageTickDemoteBuildProg {w : ℕ} {ctx : PageArenaCtx} {js cur : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pageTickDemoteBuildProg (ctx, (js, cur)))) := by
  have hm32 := pageArenaValid_meta32 hv
  have hw32 := pageArenaValid_const_lt hv
  rcases ctx with ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩
  dsimp only [PageArenaLayout.ofCtx] at hm32
  unfold pageTickDemoteBuildProg
  refine validHistory_readFullPages_bind hwf hm32 fun fp hfp1 hfp2 => ?_
  refine validHistory_bind_page hwf hv (validHistory_pageReadTailCountsProg hm32)
    fun _ _ hwf1 hv1 => ?_
  simp only [pure_bind]
  have hm1 := pageArenaValid_meta32 hv1
  dsimp only [PageArenaLayout.ofCtx] at hm1
  refine validHistory_read_bind (by split_ifs <;> omega) ?_
  refine validHistory_ite _ (fun _ => ?_) (fun _ => trivial)
  refine validHistory_ite _ (fun _ => ?_) (fun _ => trivial)
  have hsb : (if js = 0 then 0 else 1) < 2 ^ w := by split_ifs <;> omega
  exact validHistory_pageTickDemoteBuildCheckProg hwf1 hv1 hsb hfp1 hfp2

/-- Memory history admissibility for `pageTickBoundedProg`. -/
theorem validHistory_pageTickBoundedProg {w : ℕ} {ctx : PageArenaCtx} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pageTickBoundedProg ctx)) := by
  have hm32 := pageArenaValid_meta32 hv
  rcases ctx with ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩
  dsimp only [PageArenaLayout.ofCtx] at hm32
  unfold pageTickBoundedProg
  refine validHistory_read_bind (by omega) ?_
  refine validHistory_bind_page hwf hv (validHistory_pageReadJobArgsProg hm32)
    fun _ _ hwf1 hv1 => ?_
  dsimp only
  refine validHistory_ite _
    (fun _ => validHistory_bind_page_ro hv1 (validHistory_pageTickPromoteProg hwf1 hv1)
      fun _ _ hv2 => validHistory_pageMaybeStartJobProg hv2) fun _ =>
    validHistory_ite _
      (fun _ => validHistory_bind_page_ro hv1 (validHistory_pageTickDemoteSwapProg hwf1 hv1)
        fun _ _ hv2 => validHistory_pageMaybeStartJobProg hv2) fun _ =>
      validHistory_ite _
        (fun _ => validHistory_bind_page_ro hv1 (validHistory_pageTickDemoteBuildProg hwf1 hv1)
          fun _ _ hv2 => validHistory_pageMaybeStartJobProg hv2) fun _ =>
        validHistory_pageMaybeStartJobProg hv1

/-- Memory history admissibility for `pageRunTicksBatchProg`. -/
theorem validHistory_pageRunTicksBatchProg {w : ℕ} {ctx : PageArenaCtx} {fuel : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pageRunTicksBatchProg (ctx, fuel))) := by
  unfold pageRunTicksBatchProg pageRunTicksIterProg
  refine validHistory_bind_ro ?_ fun _ _ _ => trivial
  exact validHistory_iterate_wf fuel 0 s hwf hv
    (fun _ _ hle h => pageArenaValid_mono h hle)
    (fun _ _ hwf' hv' => by
      unfold pageTickIterStepProg
      exact validHistory_bind_ro (validHistory_pageTickBoundedProg hwf' hv') fun _ _ _ => trivial)

/-! ## Section 5: `LargePageProg` Unpermutation, Append, and PopBack Programs -/

/-- Memory history admissibility for `pageBeginUnpermBoundedProg`. -/
theorem validHistory_pageBeginUnpermBoundedProg {w : ℕ} {ctx : PageArenaCtx}
    {s : Memory.State} (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pageBeginUnpermBoundedProg ctx)) := by
  have hm32 := pageArenaValid_meta32 hv
  have hw32 := pageArenaValid_const_lt hv
  rcases ctx with ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩
  dsimp only [PageArenaLayout.ofCtx] at hm32
  unfold pageBeginUnpermBoundedProg
  refine validHistory_read_bind (by omega) ?_
  refine validHistory_bind_page_ro hv (validHistory_pageReadFullPagesProg hm32) fun _ _ hv1 => ?_
  have hm1 := pageArenaValid_meta32 hv1
  dsimp only [PageArenaLayout.ofCtx] at hm1
  refine validHistory_bind_page_ro hv1 (validHistory_pageReadTailCountsProg hm1) fun _ _ hv2 => ?_
  have hm2 := pageArenaValid_meta32 hv2
  dsimp only [PageArenaLayout.ofCtx] at hm2
  refine validHistory_ite _ (fun _ => ?_) (fun _ => trivial)
  refine validHistory_read_bind (by omega) ?_
  simp only [pure_bind]
  exact validHistory_pageWriteCleanProg hm2 (by split_ifs <;> omega)
    (Nat.two_pow_pos w) (Nat.two_pow_pos w)

private theorem validHistory_pageWriteOwnerVpOnlyProg {w : ℕ} {ctx : PageArenaCtx} {P vp : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pageWriteOwnerVpOnlyProg ((ctx, P), vp))) := by
  rcases ctx with ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩
  obtain ⟨hw, hwv, hpb, _, _, _, _, _, _, _, _, _, ho2, hm_ib, hib_fr⟩ := hv
  dsimp only [PageArenaLayout.ofCtx] at hwv hpb ho2 hm_ib hib_fr
  subst hwv
  unfold pageWriteOwnerVpOnlyProg
  refine validHistory_ite (P < mp) (fun _ => ?_) (fun _ => trivial)
  exact validHistory_writePackedCompGen hwf ⟨4 * mp, hw, rfl, hpb, by omega, by omega⟩

private theorem validHistory_pageCommitCleanDirProg {w : ℕ} {ctx : PageArenaCtx}
    {cvp pCur vpOther : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s
        (pageCommitCleanDirProg (ctx, (cvp, (pCur, vpOther))))) := by
  unfold pageCommitCleanDirProg
  simp only [pure_bind]
  refine validHistory_bind_page hwf hv (validHistory_pageWritePageOfProg hwf hv)
    fun _ _ hwf1 hv1 => ?_
  refine validHistory_bind_page hwf1 hv1 (validHistory_pageWritePageOfProg hwf1 hv1)
    fun _ _ hwf2 hv2 => ?_
  refine validHistory_bind_page hwf2 hv2 (validHistory_pageWriteOwnerVpOnlyProg hwf2 hv2)
    fun _ _ hwf3 hv3 => validHistory_pageWriteOwnerVpOnlyProg hwf3 hv3

private theorem validHistory_pageFinishCleanStepProg {w : ℕ} {ctx : PageArenaCtx} {cvp : ℕ}
    {s : Memory.State} (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pageFinishCleanStepProg (ctx, cvp))) := by
  have hw32 := pageArenaValid_const_lt hv
  have hmp4 := pageArenaValid_mp4_lt hv
  rcases ctx with ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩
  dsimp only [PageArenaLayout.ofCtx] at hmp4
  unfold pageFinishCleanStepProg
  refine validHistory_bind_page_ro hv (validHistory_pageMaybeStartJobProg hv) fun _ _ hv1 => ?_
  have hm32 := pageArenaValid_meta32 hv1
  dsimp only [PageArenaLayout.ofCtx] at hm32
  refine validHistory_read_bind (by omega) ?_
  refine validHistory_read_bind (by omega) ?_
  refine validHistory_ite _ (fun hq1 => ?_) (fun _ => trivial)
  simp only [pure_bind]
  refine validHistory_pageWriteCleanProg hm32 (by split_ifs <;> omega) ?_ (Nat.two_pow_pos w)
  split_ifs <;> omega

private theorem validHistory_pageUnpermPhase2ZeroProg {w : ℕ} {ctx : PageArenaCtx}
    {cvp q1 : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier) (hq1 : q1 < 2 ^ w) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pageUnpermPhase2ZeroProg (ctx, (cvp, q1)))) := by
  have hm32 := pageArenaValid_meta32 hv
  have hw32 := pageArenaValid_const_lt hv
  rcases ctx with ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩
  dsimp only [PageArenaLayout.ofCtx] at hm32
  unfold pageUnpermPhase2ZeroProg
  refine validHistory_ite (q1 ≤ cvp) (fun _ => ?_) (fun hlt => ?_)
  · simp only [pure_bind]
    exact validHistory_pageWriteCleanProg hm32 (by omega) (Nat.two_pow_pos w) (Nat.two_pow_pos w)
  · simp only [pure_bind]
    refine validHistory_bind_page hwf hv (validHistory_pageReadPageOfProg hv)
      fun _ _ hwf1 hv1 => ?_
    have hm1 := pageArenaValid_meta32 hv1
    dsimp only [PageArenaLayout.ofCtx] at hm1
    refine validHistory_ite _ (fun _ => ?_) (fun _ => ?_)
    · exact validHistory_pageWriteCleanProg hm1 (by omega) (by omega) (Nat.two_pow_pos w)
    · refine validHistory_ite _ (fun _ => ?_) (fun _ => trivial)
      unfold pageUnpermPhase2ZeroSwapProg
      simp only [pure_bind]
      refine validHistory_bind_page hwf1 hv1 (validHistory_pageSwapPhysProg hwf1 hv1)
        fun _ _ _ hv2 => ?_
      have hm2 := pageArenaValid_meta32 hv2
      dsimp only [PageArenaLayout.ofCtx] at hm2
      exact validHistory_pageWriteCleanProg hm2 (by omega) (by omega) (by omega)

private theorem validHistory_pageUnpermPhase2MidProg {w : ℕ} {ctx : PageArenaCtx}
    {cvp coff q1 : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier)
    (hcoff : coff < (PageArenaLayout.ofCtx ctx).pgB) (hq1 : q1 < 2 ^ w) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pageUnpermPhase2MidProg (ctx, ((cvp, coff), q1)))) := by
  have hpg16 := pageArenaValid_pg16_lt hv
  have hw32 := pageArenaValid_const_lt hv
  unfold pageUnpermPhase2MidProg
  refine validHistory_ite (cvp < q1) (fun hlt => ?_) (fun _ => trivial)
  simp only [pure_bind]
  refine validHistory_bind_page hwf hv (validHistory_pageReadPageOfProg hv)
    fun _ _ hwf1 hv1 => ?_
  refine validHistory_ite _ (fun _ => ?_) (fun _ => trivial)
  rcases ctx with ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩
  dsimp only [PageArenaLayout.ofCtx] at hpg16 hcoff
  unfold pageUnpermPhase2MidSwapProg
  simp only [pure_bind]
  refine validHistory_bind_page hwf1 hv1 (validHistory_pageSwapPhysProg hwf1 hv1)
    fun _ _ _ hv2 => ?_
  have hm2 := pageArenaValid_meta32 hv2
  dsimp only [PageArenaLayout.ofCtx] at hm2
  exact validHistory_pageWriteCleanProg hm2 (by omega) (by omega) (by omega)

private theorem validHistory_pageUnpermPhase2EndProg {w : ℕ} {ctx : PageArenaCtx}
    {cvp q1 : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pageUnpermPhase2EndProg (ctx, (cvp, q1)))) := by
  unfold pageUnpermPhase2EndProg
  refine validHistory_ite (cvp < q1) (fun _ => ?_) (fun _ => trivial)
  simp only [pure_bind]
  refine validHistory_bind_page hwf hv (validHistory_pageReadPageOfProg hv)
    fun _ _ hwf1 hv1 => ?_
  refine validHistory_bind_page hwf1 hv1 (validHistory_pageReadOwnerProg hv1)
    fun _ _ hwf2 hv2 => ?_
  exact validHistory_bind_page_ro hv2 (validHistory_pageCommitCleanDirProg hwf2 hv2)
    fun _ _ hv3 => validHistory_pageFinishCleanStepProg hv3

private theorem validHistory_pageUnpermPhase2Prog {w : ℕ} {ctx : PageArenaCtx}
    {cvp coff : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pageUnpermPhase2Prog (ctx, (cvp, coff)))) := by
  have hm32 := pageArenaValid_meta32 hv
  have hmp4 := pageArenaValid_mp4_lt hv
  rcases ctx with ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩
  dsimp only [PageArenaLayout.ofCtx] at hm32 hmp4
  unfold pageUnpermPhase2Prog
  refine validHistory_read_bind (by omega) ?_
  refine validHistory_ite _ (fun hgd => ?_) (fun _ => trivial)
  obtain ⟨_, hq1_mp⟩ := hgd
  refine validHistory_ite (coff = 0)
    (fun _ => validHistory_pageUnpermPhase2ZeroProg hwf hv (by omega)) fun _ =>
    validHistory_ite (coff < pg)
      (fun hlt => validHistory_pageUnpermPhase2MidProg hwf hv hlt (by omega))
      (fun _ => validHistory_pageUnpermPhase2EndProg hwf hv)

private theorem validHistory_pageUnpermPhase3Prog {w : ℕ} {ctx : PageArenaCtx} {cvp : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier) (hcvp : cvp < 2 ^ w) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pageUnpermPhase3Prog (ctx, cvp))) := by
  have hm32 := pageArenaValid_meta32 hv
  have hpg16 := pageArenaValid_pg16_lt hv
  have hw32 := pageArenaValid_const_lt hv
  rcases ctx with ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩
  dsimp only [PageArenaLayout.ofCtx] at hm32 hpg16
  unfold pageUnpermPhase3Prog
  refine validHistory_read_bind (by omega) ?_
  refine validHistory_read_bind (by omega) ?_
  refine validHistory_ite _ (fun _ => ?_) (fun hlt => ?_)
  · simp only [pure_bind]
    exact validHistory_pageWriteCleanProg hm32 (by omega) hcvp (Nat.two_pow_pos w)
  · refine validHistory_ite _ (fun hgd => ?_) (fun _ => trivial)
    obtain ⟨_, hr1_lt, _⟩ := hgd
    simp only [pure_bind]
    unfold pageUnpermPhase3SwapProg
    simp only [pure_bind]
    refine validHistory_bind_page hwf hv (validHistory_pageTailPhysBoundedProg hv)
      fun _ _ hwf1 hv1 => ?_
    refine validHistory_bind_page hwf1 hv1 (validHistory_pageSwapTailSlotsProg hwf1 hv1)
      fun _ _ _ hv2 => ?_
    have hm2 := pageArenaValid_meta32 hv2
    dsimp only [PageArenaLayout.ofCtx] at hm2
    exact validHistory_pageWriteCleanProg hm2 (by omega) (by omega) (Nat.two_pow_pos w)

private theorem validHistory_pageUnpermPhase1Prog {w : ℕ} {ctx : PageArenaCtx} {cvp : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pageUnpermPhase1Prog (ctx, cvp))) := by
  have hm32 := pageArenaValid_meta32 hv
  have hw32 := pageArenaValid_const_lt hv
  rcases ctx with ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩
  dsimp only [PageArenaLayout.ofCtx] at hm32
  unfold pageUnpermPhase1Prog
  refine validHistory_read_bind (by omega) ?_
  refine validHistory_read_bind_wf hwf (by omega) fun q1 hq1_w => ?_
  refine validHistory_ite _ (fun _ => ?_) (fun _ => ?_)
  · simp only [pure_bind]
    refine validHistory_pageWriteCleanProg hm32 (by omega) ?_ (Nat.two_pow_pos w)
    split_ifs <;> omega
  · unfold pageUnpermPhase1TickProg
    refine validHistory_bind_page hwf hv (validHistory_pageTickBoundedProg hwf hv)
      fun _ _ hwf1 hv1 => ?_
    have hm1 := pageArenaValid_meta32 hv1
    dsimp only [PageArenaLayout.ofCtx] at hm1
    refine validHistory_read_bind_wf hwf1 (by omega) fun q1' hq1'_w => ?_
    simp only [pure_bind]
    refine validHistory_pageWriteCleanProg hm1 (by omega) ?_ (Nat.two_pow_pos w)
    split_ifs <;> omega

/-- Memory history admissibility for `pageUnpermStepBoundedProg`. -/
theorem validHistory_pageUnpermStepBoundedProg {w : ℕ} {ctx : PageArenaCtx} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pageUnpermStepBoundedProg ctx)) := by
  have hm32 := pageArenaValid_meta32 hv
  rcases ctx with ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩
  dsimp only [PageArenaLayout.ofCtx] at hm32
  unfold pageUnpermStepBoundedProg
  refine validHistory_read_bind (by omega) ?_
  refine validHistory_readCleanPos_bind hwf hm32 fun co hcvp_w _ => ?_
  exact validHistory_ite _ (fun _ => validHistory_pageUnpermPhase1Prog hwf hv) fun _ =>
    validHistory_ite _ (fun _ => validHistory_pageUnpermPhase2Prog hwf hv) fun _ =>
      validHistory_ite _ (fun _ => validHistory_pageUnpermPhase3Prog hwf hv hcvp_w) fun _ =>
        trivial

/-- Memory history admissibility for `pageRunUnpermBatchProg`. -/
theorem validHistory_pageRunUnpermBatchProg {w : ℕ} {ctx : PageArenaCtx} {fuel : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pageRunUnpermBatchProg (ctx, fuel))) := by
  unfold pageRunUnpermBatchProg pageRunUnpermIterProg
  refine validHistory_bind_ro ?_ fun _ _ _ => trivial
  exact validHistory_iterate_wf fuel 0 s hwf hv
    (fun _ _ hle h => pageArenaValid_mono h hle)
    (fun _ _ hwf' hv' => by
      unfold pageUnpermIterStepProg
      exact validHistory_bind_ro (validHistory_pageUnpermStepBoundedProg hwf' hv')
        fun _ _ _ => trivial)

private theorem validHistory_pageRawAppendProg {w : ℕ} {ctx : PageArenaCtx} {sb : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pageRawAppendProg (ctx, sb))) := by
  have hm32 := pageArenaValid_meta32 hv
  have hpg16 := pageArenaValid_pg16_lt hv
  rcases ctx with ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩
  dsimp only [PageArenaLayout.ofCtx] at hm32 hpg16
  unfold pageRawAppendProg
  refine validHistory_bind_page hwf hv (validHistory_pageReadFullPagesProg hm32)
    fun _ _ hwf1 hv1 => ?_
  have hm1 := pageArenaValid_meta32 hv1
  dsimp only [PageArenaLayout.ofCtx] at hm1
  refine validHistory_bind_page hwf1 hv1 (validHistory_pageReadTailCountsProg hm1)
    fun _ _ hwf2 hv2 => ?_
  have hm2 := pageArenaValid_meta32 hv2
  dsimp only [PageArenaLayout.ofCtx] at hm2
  simp only [pure_bind]
  refine validHistory_read_bind (by split_ifs <;> omega) ?_
  refine validHistory_ite _ (fun _ => ?_) (fun _ => trivial)
  refine validHistory_ite _ (fun _ => ?_) (fun _ => trivial)
  unfold pageRawAppendCheckProg
  refine validHistory_ite _ (fun _ => ?_) (fun _ => trivial)
  refine validHistory_ite _ (fun _ => ?_) (fun _ => trivial)
  simp only [pure_bind]
  refine validHistory_ite _ (fun hrs => ?_) (fun _ => trivial)
  unfold pageRawAppendCommitProg
  simp only [pure_bind]
  refine validHistory_write_bind_wf hwf2 (by split_ifs <;> omega) (by omega)
    fun s₃ hwf₃ hfr₃ => ?_
  have hv3 : (PageArenaLayout.ofCtx
      ((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc))).Valid w s₃.frontier :=
    hfr₃.symm ▸ hv2
  refine validHistory_bind_page hwf₃ hv3 (validHistory_pageWriteTailResProg hwf₃ hv3)
    fun _ _ hwf4 hv4 => validHistory_pageWriteTailOwnerProg hwf4 hv4

private theorem validHistory_pageZeroPhaseRebalanceProg {w : ℕ} {ctx : PageArenaCtx}
    {tickFuel : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pageZeroPhaseRebalanceProg (ctx, tickFuel))) := by
  rcases ctx with ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩
  unfold pageZeroPhaseRebalanceProg
  refine validHistory_bind_page hwf hv (validHistory_pageMaybeStartJobProg hv)
    fun _ _ hwf1 hv1 => ?_
  refine validHistory_bind_page_ro hv1 (validHistory_pageRunTicksBatchProg hwf1 hv1)
    fun _ _ hv2 => ?_
  simp only [pure_bind]
  have hm32 := pageArenaValid_meta32 hv2
  dsimp only [PageArenaLayout.ofCtx] at hm32
  have hpow0 : 0 < 2 ^ w := Nat.two_pow_pos w
  exact validHistory_pageWriteCleanProg hm32 hpow0 hpow0 hpow0

private theorem validHistory_pageRebalanceSyncCleanProg {w : ℕ} {ctx : PageArenaCtx}
    {tickFuel cvp : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s
        (pageRebalanceSyncCleanProg ((ctx, tickFuel), cvp))) := by
  have hw32 := pageArenaValid_const_lt hv
  rcases ctx with ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩
  unfold pageRebalanceSyncCleanProg
  refine validHistory_bind_page hwf hv (validHistory_pageMaybeStartJobProg hv)
    fun _ _ hwf1 hv1 => ?_
  refine validHistory_bind_page hwf1 hv1 (validHistory_pageRunTicksBatchProg hwf1 hv1)
    fun _ _ hwf2 hv2 => ?_
  have hm32 := pageArenaValid_meta32 hv2
  dsimp only [PageArenaLayout.ofCtx] at hm32
  refine validHistory_read_bind (by omega) ?_
  refine validHistory_read_bind_wf hwf2 (by omega) fun q1 hq1_w => ?_
  simp only [pure_bind]
  refine validHistory_pageWriteCleanProg hm32 (by split_ifs <;> omega) ?_ (Nat.two_pow_pos w)
  split_ifs <;> omega

/-- Memory history admissibility for `pageAppendBoundedProg`. -/
theorem validHistory_pageAppendBoundedProg {w : ℕ} {ctx : PageArenaCtx} {sb tickFuel : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pageAppendBoundedProg ((ctx, sb), tickFuel))) := by
  have hm32 := pageArenaValid_meta32 hv
  rcases ctx with ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩
  dsimp only [PageArenaLayout.ofCtx] at hm32
  unfold pageAppendBoundedProg
  refine validHistory_read_bind (by omega) ?_
  refine validHistory_bind_page hwf hv (validHistory_pageReadCleanPosProg hm32)
    fun _ _ hwf1 hv1 => ?_
  refine validHistory_bind_page hwf1 hv1 (validHistory_pageRawAppendProg hwf1 hv1)
    fun _ _ hwf2 hv2 => ?_
  exact validHistory_ite _ (fun _ => validHistory_pageZeroPhaseRebalanceProg hwf2 hv2) fun _ =>
    validHistory_ite _ (fun _ => validHistory_pageRebalanceSyncCleanProg hwf2 hv2) fun _ =>
      trivial

private theorem validHistory_pageRawPopBackProg {w : ℕ} {ctx : PageArenaCtx} {sb : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pageRawPopBackProg (ctx, sb))) := by
  have hm32 := pageArenaValid_meta32 hv
  rcases ctx with ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩
  dsimp only [PageArenaLayout.ofCtx] at hm32
  unfold pageRawPopBackProg
  refine validHistory_bind_page hwf hv (validHistory_pageReadFullPagesProg hm32)
    fun _ _ hwf1 hv1 => ?_
  have hm1 := pageArenaValid_meta32 hv1
  dsimp only [PageArenaLayout.ofCtx] at hm1
  refine validHistory_readTailCounts_bind hwf1 hm1 fun tc htc1 htc2 => ?_
  simp only [pure_bind]
  refine validHistory_ite _ (fun _ => ?_) (fun _ => trivial)
  refine validHistory_ite _ (fun _ => ?_) (fun _ => trivial)
  unfold pageRawPopBackCheckProg
  refine validHistory_ite _ (fun _ => ?_) (fun _ => trivial)
  refine validHistory_ite _ (fun _ => ?_) (fun _ => trivial)
  simp only [pure_bind]
  refine validHistory_ite _ (fun _ => ?_) (fun _ => trivial)
  unfold pageRawPopBackCommitProg
  simp only [pure_bind]
  refine validHistory_bind_page hwf1 hv1 (validHistory_pageTailPhysBoundedProg hv1)
    fun _ _ hwf2 hv2 => ?_
  refine validHistory_bind_page hwf2 hv2 (validHistory_pageSwapTailSlotsProg hwf2 hv2)
    fun _ _ _ hv3 => ?_
  have hm3 := pageArenaValid_meta32 hv3
  dsimp only [PageArenaLayout.ofCtx] at hm3
  exact validHistory_write_only (by split_ifs <;> omega) (by split_ifs <;> omega)

private theorem validHistory_pagePopBackTailCleanProg {w mb ph cvp coff : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hfr : mb + 32 ≤ s.frontier) (hw32 : 32 < 2 ^ w)
    (hph : ph < 2 ^ w) (hcvp : cvp < 2 ^ w) (hcoff : coff < 2 ^ w) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pagePopBackTailCleanProg ((mb, ph), (cvp, coff)))) := by
  unfold pagePopBackTailCleanProg
  refine validHistory_ite (ph = 2) ?_ ?_
  · intro _
    simp only [pure_bind]
    exact validHistory_pageWriteCleanProg hfr (by omega) hcvp hcoff
  · intro _
    refine validHistory_read_bind_wf hwf (by omega) fun r1 hr1_w => ?_
    simp only [pure_bind]
    refine validHistory_pageWriteCleanProg hfr hph ?_ (Nat.two_pow_pos w)
    split_ifs <;> omega

/-- Memory history admissibility for `pagePopBackBoundedProg`. -/
theorem validHistory_pagePopBackBoundedProg {w : ℕ} {ctx : PageArenaCtx} {sb tickFuel : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (PageArenaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pagePopBackBoundedProg ((ctx, sb), tickFuel))) := by
  have hm32 := pageArenaValid_meta32 hv
  have hw32 := pageArenaValid_const_lt hv
  rcases ctx with ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩
  dsimp only [PageArenaLayout.ofCtx] at hm32
  unfold pagePopBackBoundedProg
  refine validHistory_read_bind_wf hwf (by omega) fun ph hph_w => ?_
  refine validHistory_readCleanPos_bind hwf hm32 fun co hcvp_w hcoff_w => ?_
  refine validHistory_bind_page hwf hv (validHistory_pageRawPopBackProg hwf hv)
    fun _ _ hwf1 hv1 => ?_
  have hm1 := pageArenaValid_meta32 hv1
  dsimp only [PageArenaLayout.ofCtx] at hm1
  exact validHistory_ite _ (fun _ => validHistory_pageZeroPhaseRebalanceProg hwf1 hv1) fun _ =>
    validHistory_ite _ (fun _ => validHistory_pageRebalanceSyncCleanProg hwf1 hv1) fun _ =>
      validHistory_pagePopBackTailCleanProg hwf1 hm1 hw32 hph_w hcvp_w hcoff_w

/-! ## Section 6: Unified `SlotIoLayout` Programs (`LargeBlockPool`) -/

/-- Memory history admissibility for `slotIoReadRawProg`. -/
theorem validHistory_slotIoReadRawProg {w : ℕ} {ctx : SlotIoCtx} {idx : ℕ} {s : Memory.State}
    (hv : (SlotIoLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (slotIoReadRawProg (ctx, idx))) := by
  rcases ctx with ⟨⟨up, sb⟩, ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩⟩
  unfold slotIoReadRawProg
  refine validHistory_ite (up = 0) ?_ ?_
  · intro h0
    unfold SlotIoLayout.Valid SlotIoLayout.ofCtx PageArenaLayout.ofCtx at hv
    dsimp only at hv
    rw [ite_eq_left h0] at hv
    obtain ⟨hw, hwv, hqb, hvb, _, htail⟩ := hv
    subst hwv
    refine validHistory_ite (idx < nc) (fun hidx => ?_) (fun _ => trivial)
    refine validHistory_ite (sb = 0) ?_ ?_
    · intro hsb
      rw [ite_eq_left hsb] at htail
      have hlt := wOffV_add_one_lt_pairStreamWords (q_bits := qb) (v_bits := vb) hw hidx
      exact validHistory_readPairGenProg ⟨hw, rfl, hqb, hvb, by omega⟩
    · intro hsb
      rw [ite_eq_right hsb] at htail
      obtain ⟨hq_ot, hot_w, hmb_od, hod_ib, hib_fr⟩ := htail
      have h2 := pairStreamWords_ge_two nc ot vb w
      refine validHistory_read_bind (by omega) ?_
      refine validHistory_ite (idx < s.mem mb) ?_ ?_
      · intro _
        have hlt := wOffV_add_one_lt_pairStreamWords (q_bits := qb) (v_bits := vb) hw hidx
        have hmono := pairStreamWords_mono_qBits (n := nc) (v := vb) (w := w) hq_ot
        exact validHistory_readPairGenProg ⟨hw, rfl, hqb, hvb, by omega⟩
      · intro _
        have hlt := wOffV_add_one_lt_pairStreamWords (q_bits := ot) (v_bits := vb) hw hidx
        refine validHistory_bind_ro
          (validHistory_readPairGenProg ⟨hw, rfl, hot_w, hvb, by omega⟩)
          fun _ _ _ => ?_
        exact validHistory_ite (qb < w) (fun _ => by simp only [pure_bind]; trivial)
          (fun _ => trivial)
  · intro h0
    unfold SlotIoLayout.Valid SlotIoLayout.ofCtx at hv
    dsimp only at hv
    rw [ite_eq_right h0] at hv
    simp only [pure_bind]
    exact validHistory_pageReadVirtBoundedProg hv

/-- Memory history admissibility for `slotIoWriteRawProg`. -/
theorem validHistory_slotIoWriteRawProg {w : ℕ} {ctx : SlotIoCtx} {idx : ℕ} {qv : ℕ × ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (SlotIoLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (slotIoWriteRawProg ((ctx, idx), qv))) := by
  rcases ctx with ⟨⟨up, sb⟩, ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩⟩
  unfold slotIoWriteRawProg
  refine validHistory_ite (up = 0) ?_ ?_
  · intro h0
    unfold SlotIoLayout.Valid SlotIoLayout.ofCtx PageArenaLayout.ofCtx at hv
    dsimp only at hv
    rw [ite_eq_left h0] at hv
    obtain ⟨hw, hwv, hqb, hvb, _, htail⟩ := hv
    subst hwv
    refine validHistory_ite (idx < nc) (fun hidx => ?_) (fun _ => trivial)
    refine validHistory_ite (sb = 0) ?_ ?_
    · intro hsb
      rw [ite_eq_left hsb] at htail
      have hlt := wOffV_add_one_lt_pairStreamWords (q_bits := qb) (v_bits := vb) hw hidx
      exact validHistory_writePairGenProg hwf ⟨hw, rfl, hqb, hvb, by omega⟩
    · intro hsb
      rw [ite_eq_right hsb] at htail
      obtain ⟨hq_ot, hot_w, hmb_od, hod_ib, hib_fr⟩ := htail
      have h2 := pairStreamWords_ge_two nc ot vb w
      refine validHistory_read_bind (by omega) ?_
      refine validHistory_ite (idx < s.mem mb) ?_ ?_
      · intro _
        have hlt := wOffV_add_one_lt_pairStreamWords (q_bits := qb) (v_bits := vb) hw hidx
        have hmono := pairStreamWords_mono_qBits (n := nc) (v := vb) (w := w) hq_ot
        exact validHistory_writePairGenProg hwf ⟨hw, rfl, hqb, hvb, by omega⟩
      · intro _
        have hlt := wOffV_add_one_lt_pairStreamWords (q_bits := ot) (v_bits := vb) hw hidx
        exact validHistory_writePairGenProg hwf ⟨hw, rfl, hot_w, hvb, by omega⟩
  · intro h0
    unfold SlotIoLayout.Valid SlotIoLayout.ofCtx at hv
    dsimp only at hv
    rw [ite_eq_right h0] at hv
    simp only [pure_bind]
    exact validHistory_pageWriteVirtBoundedProg hwf hv

/-- Memory history admissibility for `slotIoSwapRawProg`. -/
theorem validHistory_slotIoSwapRawProg {w : ℕ} {ctx : SlotIoCtx} {p₁ p₂ : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (SlotIoLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (slotIoSwapRawProg (ctx, (p₁, p₂)))) := by
  unfold slotIoSwapRawProg
  refine validHistory_ite (p₁ = p₂) (fun _ => trivial) (fun _ => ?_)
  refine validHistory_bind_wf hwf (validHistory_slotIoReadRawProg hv) fun _ _ hwf1 hf1 => ?_
  have hv1 := slotIoValid_mono hv hf1
  refine validHistory_bind_wf hwf1 (validHistory_slotIoReadRawProg hv1) fun _ _ hwf2 hf2 => ?_
  have hv2 := slotIoValid_mono hv1 hf2
  refine validHistory_bind_wf hwf2 (validHistory_slotIoWriteRawProg hwf2 hv2)
    fun _ _ hwf3 hf3 => validHistory_slotIoWriteRawProg hwf3 (slotIoValid_mono hv2 hf3)

/-- Memory history admissibility for `slotIoAppendRawProg`. -/
theorem validHistory_slotIoAppendRawProg {w : ℕ} {ctx : SlotIoCtx} {nSide : ℕ}
    {qv : ℕ × ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (SlotIoLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (slotIoAppendRawProg ((ctx, nSide), qv))) := by
  rcases ctx with ⟨⟨up, sb⟩, ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩⟩
  unfold slotIoAppendRawProg
  refine validHistory_ite (up = 0) ?_ ?_
  · intro h0
    unfold SlotIoLayout.Valid SlotIoLayout.ofCtx PageArenaLayout.ofCtx at hv
    dsimp only at hv
    rw [ite_eq_left h0] at hv
    obtain ⟨hw, hwv, hqb, hvb, _, htail⟩ := hv
    subst hwv
    refine validHistory_ite (nSide < nc) (fun hidx => ?_) (fun _ => trivial)
    refine validHistory_ite (sb = 0) ?_ ?_
    · intro hsb
      rw [ite_eq_left hsb] at htail
      have hlt := wOffV_add_one_lt_pairStreamWords (q_bits := qb) (v_bits := vb) hw hidx
      exact validHistory_writePairGenProg hwf ⟨hw, rfl, hqb, hvb, by omega⟩
    · intro hsb
      rw [ite_eq_right hsb] at htail
      obtain ⟨hq_ot, hot_w, hmb_od, hod_ib, hib_fr⟩ := htail
      have h2 := pairStreamWords_ge_two nc ot vb w
      refine validHistory_read_bind (by omega) ?_
      refine validHistory_ite (nSide < s.mem mb) ?_ ?_
      · intro _
        have hlt := wOffV_add_one_lt_pairStreamWords (q_bits := qb) (v_bits := vb) hw hidx
        have hmono := pairStreamWords_mono_qBits (n := nc) (v := vb) (w := w) hq_ot
        exact validHistory_writePairGenProg hwf ⟨hw, rfl, hqb, hvb, by omega⟩
      · intro _
        have hlt := wOffV_add_one_lt_pairStreamWords (q_bits := ot) (v_bits := vb) hw hidx
        exact validHistory_writePairGenProg hwf ⟨hw, rfl, hot_w, hvb, by omega⟩
  · intro h0
    unfold SlotIoLayout.Valid SlotIoLayout.ofCtx at hv
    dsimp only at hv
    rw [ite_eq_right h0] at hv
    simp only [pure_bind]
    refine validHistory_bind_page hwf hv (validHistory_pageAppendBoundedProg hwf hv)
      fun _ _ hwf1 hv1 => validHistory_pageWriteVirtBoundedProg hwf1 hv1

/-- Memory history admissibility for `slotIoPopBackRawProg`. -/
theorem validHistory_slotIoPopBackRawProg {w : ℕ} {ctx : SlotIoCtx} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hv : (SlotIoLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (slotIoPopBackRawProg ctx)) := by
  rcases ctx with ⟨⟨up, sb⟩, pctx⟩
  unfold SlotIoLayout.Valid SlotIoLayout.ofCtx at hv
  dsimp only at hv
  unfold slotIoPopBackRawProg
  refine validHistory_ite (up = 0) (fun _ => trivial) (fun h0 => ?_)
  rw [ite_eq_right h0] at hv
  simp only [pure_bind]
  exact validHistory_pagePopBackBoundedProg hwf hv

/-! ## Section 7: Small-Regime Epoch Programs (`LargeEpochState`) -/

/-- Memory history admissibility for `smallEpochInitProg`. -/
theorem validHistory_smallEpochInitProg {w mb : ℕ} {s : Memory.State}
    (hmb : mb + 2 ≤ s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (smallEpochInitProg mb)) := by
  unfold smallEpochInitProg
  have hpow0 : 0 < 2 ^ w := Nat.two_pow_pos w
  exact validHistory_write_bind (by omega) hpow0 fun _ h1 =>
    validHistory_write_only (by omega) hpow0

private theorem validHistory_smallEpochScanStepProg {w mb nSide u_key : ℕ} {ioctx : SlotIoCtx}
    {acc : (ℕ × ℕ) × (ℕ × ℕ)} {s : Memory.State}
    (hmb : mb + 2 ≤ s.frontier) (hv : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s
        (smallEpochScanStepProg ((ioctx, (mb, (nSide, u_key))), acc))) := by
  rcases acc with ⟨⟨cur, found⟩, ⟨hitIdx, hitVal⟩⟩
  unfold smallEpochScanStepProg
  refine validHistory_read_bind (by omega) ?_
  refine validHistory_ite (cur < nSide) (fun _ => ?_) (fun _ => trivial)
  refine validHistory_bind_ro (validHistory_slotIoReadRawProg hv) fun _ _ _ => ?_
  exact validHistory_ite _ (fun _ => trivial) (fun _ => trivial)

private theorem validHistory_smallEpochScanRawProg {w mb u_key : ℕ} {ioctx : SlotIoCtx}
    {s : Memory.State} (hmb : mb + 2 ≤ s.frontier)
    (hv : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (smallEpochScanRawProg ((ioctx, mb), u_key))) := by
  unfold smallEpochScanRawProg
  refine validHistory_read_bind (by omega) ?_
  refine validHistory_ite _ (fun _ => ?_) (fun _ => trivial)
  simp only [pure_bind]
  unfold smallEpochScanLoopProg
  refine validHistory_bind_ro ?_ fun _ _ _ => trivial
  exact validHistory_iterate_inv (Inv := fun _ s' => s' = s)
    (s.mem (mb + 1)) ((0, 0), (0, 0)) s rfl
    (fun _ s' hs' => hs'.symm ▸ validHistory_smallEpochScanStepProg hmb hv)
    (fun _ s' hs' _ => by rw [smallEpochScanStep_state_eq, hs'])

/-- Memory history admissibility for `smallEpochQueryRawProg`. -/
theorem validHistory_smallEpochQueryRawProg {w mb u_key : ℕ} {ioctx : SlotIoCtx}
    {s : Memory.State} (hmb : mb + 2 ≤ s.frontier)
    (hv : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (smallEpochQueryRawProg ((ioctx, mb), u_key))) := by
  unfold smallEpochQueryRawProg
  exact validHistory_bind_ro (validHistory_smallEpochScanRawProg hmb hv) fun _ _ _ => trivial

/-- Memory history admissibility for `smallEpochInsertRawProg`. -/
theorem validHistory_smallEpochInsertRawProg {w mb u_key v_val : ℕ} {ioctx : SlotIoCtx}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmb : mb + 2 ≤ s.frontier) (hv : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s
        (smallEpochInsertRawProg (((ioctx, mb), u_key), v_val))) := by
  have hnc_lt : (SlotIoLayout.ofCtx ioctx).pgL.nCap < 2 ^ w := slotIoValid_nCap_lt hv
  rcases ioctx with ⟨⟨up, sb⟩, ⟨⟨⟨⟨pmb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩⟩
  dsimp only [SlotIoLayout.ofCtx, PageArenaLayout.ofCtx] at hnc_lt
  unfold smallEpochInsertRawProg
  refine validHistory_bind_wf hwf (validHistory_smallEpochScanRawProg hmb hv)
    fun _ s₁ hwf₁ hf₁ => ?_
  have hv₁ := slotIoValid_mono hv hf₁
  refine validHistory_ite _ (fun _ => validHistory_slotIoWriteRawProg hwf₁ hv₁) (fun _ => ?_)
  refine validHistory_read_bind (by omega) ?_
  refine validHistory_ite _ (fun hlt => ?_) (fun _ => trivial)
  refine validHistory_bind_ro (validHistory_slotIoAppendRawProg hwf₁ hv₁) fun _ _ hf₂ => ?_
  exact validHistory_write_only (by omega) (by omega)

/-- Memory history admissibility for `smallEpochDeleteRawProg`. -/
theorem validHistory_smallEpochDeleteRawProg {w mb u_key : ℕ} {ioctx : SlotIoCtx}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmb : mb + 2 ≤ s.frontier) (hv : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (smallEpochDeleteRawProg ((ioctx, mb), u_key))) := by
  unfold smallEpochDeleteRawProg
  refine validHistory_bind_wf hwf (validHistory_smallEpochScanRawProg hmb hv)
    fun _ s₁ hwf₁ hf₁ => ?_
  have hv₁ := slotIoValid_mono hv hf₁
  refine validHistory_ite _ (fun _ => ?_) (fun _ => trivial)
  refine validHistory_read_bind_wf hwf₁ (by omega) fun nSide hn_lt => ?_
  refine validHistory_ite (0 < nSide) (fun _ => ?_) (fun _ => trivial)
  simp only [pure_bind]
  refine validHistory_bind_wf hwf₁ (validHistory_slotIoSwapRawProg hwf₁ hv₁)
    fun _ _ hwf₂ hf₂ => ?_
  refine validHistory_bind_ro (validHistory_slotIoPopBackRawProg hwf₂ (slotIoValid_mono hv₁ hf₂))
    fun _ _ hf₃ => ?_
  exact validHistory_write_only (by omega) (by omega)

/-- Memory history admissibility for `smallEpochPopAnyRawProg`. -/
theorem validHistory_smallEpochPopAnyRawProg {w mb : ℕ} {ioctx : SlotIoCtx}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmb : mb + 2 ≤ s.frontier) (hv : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (smallEpochPopAnyRawProg (ioctx, mb))) := by
  unfold smallEpochPopAnyRawProg
  refine validHistory_read_bind_wf hwf (by omega) fun nSide hn_lt => ?_
  refine validHistory_ite (0 < nSide) (fun _ => ?_) (fun _ => trivial)
  simp only [pure_bind]
  refine validHistory_bind_wf hwf (validHistory_slotIoReadRawProg hv) fun _ _ hwf₁ hf₁ => ?_
  refine validHistory_bind_ro (validHistory_slotIoPopBackRawProg hwf₁ (slotIoValid_mono hv hf₁))
    fun _ _ hf₂ => ?_
  exact validHistory_write_bind (by omega) (by omega) fun _ _ => trivial

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp
