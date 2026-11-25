/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.MigratePoolCongr
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.DualEpochInvBase
-- Retain private `import all` solely to unfold unexposed `Memory.Prog` bodies in the large-epoch
-- modules without modifying upstream modules or invalidating cached `.olean` artifacts.
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeMetaProg
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeBlockPool
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpochState
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpochCtx
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpochSubEpoch
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpochDrain
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpochAdvance
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpochRemBase
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpochRemove
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpochFast
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpoch
import Mathlib.Tactic.Ring

/-!
# Single-State-Anchored `RWConfined` & Direct-Mode Epoch Confinement (`MigrateSlotRw`)

This module provides the `RWConfined` region-confinement combinators and certifies read/write
confinement for large-epoch metadata helpers and direct-mode (`io.usePaged = 0`) epoch mutations
(`epochInsert_direct_rw`, `epochDelete_direct_rw`) during Phases `6..7`:

1. **Single-state-anchored read/write confinement (`RWConfined R W s₁ p`):** certifies that
   starting at `s₁` (where `ParamTable` holds), `p` reads only inside `R` and writes only inside
   `W`, automatically preserving `ParamTable` across monadic bind chains without threading dynamic
   data-structure invariants.
2. **Direct-mode (`io.usePaged = 0`) confinement (`epochInsert_direct_rw`,
   `epochDelete_direct_rw`):** certifies that source-slot mutations during Phases `6..7` stay
   strictly inside `SlotDirectRegion`, completely outside the destination epoch's hidden hash-seed
   and fast-table region.

## Main definitions

* `RWConfined`: single-state-anchored read/write region-confinement certificate.
* `SlotDirectRegion`: read/write word-address envelope of a direct-mode (`usePaged = 0`) slot.

## Main results

* `SlotCoupledStep.of_rwConfined`: lifts `RWConfined R W s₁ p` (`W ⊆ R ⊆ M`) into
  `SlotCoupledStep`.
* `epochInsert_direct_rw`, `epochDelete_direct_rw`: direct-mode (`usePaged = 0`) `RWConfined`
  certificates on `EpochSlotInv`.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.WordRAM.Resizable
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
open Cslib.DataStructure.HashFamily Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.WordRAM.Resizable.Randomized

attribute [local simp] prog_clientResult_bind prog_runClient_state_bind prog_clientResult_pure
attribute [local simp] prog_runClient_state_pure prog_clientResult_map prog_runClient_state_map
attribute [local simp] prog_clientResult_read prog_runClient_state_read

/-! ## Section 1: Single-State-Anchored `RWConfined` Combinators -/

/-- Single-state-anchored read/write confinement certificate for `p : Memory.Prog α`: starting at
`s₁`, `p` preserves `frontier`, leaves words outside `W` untouched (on both `s₁` and any `s₂`
agreeing with `s₁` on `R`), and produces equal results and `R`-agreeing post-states for any `s₂`
agreeing with `s₁` on `R`. -/
structure RWConfined {α : Type} (R W : ℕ → Prop) (s₁ : Memory.State)
    (p : Memory.Prog α) : Prop where
  /-- `frontier` is preserved on `s₁`. -/
  fr₁ : ((Memory.spec 0).clientState s₁ p).frontier = s₁.frontier
  /-- Words outside `W` are preserved on `s₁`. -/
  out₁ : ∀ addr, ¬W addr → ((Memory.spec 0).clientState s₁ p).mem addr = s₁.mem addr
  /-- `frontier` and words outside `W` are preserved on any `s₂` agreeing with `s₁` on `R`. -/
  out₂ : ∀ s₂, (∀ addr, R addr → s₁.mem addr = s₂.mem addr) →
    ((Memory.spec 0).clientState s₂ p).frontier = s₂.frontier ∧
    (∀ addr, ¬W addr → ((Memory.spec 0).clientState s₂ p).mem addr = s₂.mem addr)
  /-- Equal return values on any `s₂` agreeing with `s₁` on `R`. -/
  res_eq : ∀ s₂, (∀ addr, R addr → s₁.mem addr = s₂.mem addr) →
    (Memory.spec 0).clientResult s₁ p = (Memory.spec 0).clientResult s₂ p
  /-- Post-state agreement on `R` for any `s₂` agreeing with `s₁` on `R`. -/
  mem_in : ∀ s₂, (∀ addr, R addr → s₁.mem addr = s₂.mem addr) →
    ∀ addr, R addr →
      ((Memory.spec 0).clientState s₁ p).mem addr =
        ((Memory.spec 0).clientState s₂ p).mem addr

namespace RWConfined

/-- `pure x` satisfies `RWConfined R W s₁` for all `R, W`. -/
theorem pure_prog {α : Type} {R W : ℕ → Prop} {s₁ : Memory.State} (x : α) :
    RWConfined R W s₁ (pure x) where
  fr₁ := rfl
  out₁ _ _ := rfl
  out₂ _ _ := ⟨rfl, fun _ _ => rfl⟩
  res_eq _ _ := rfl
  mem_in _ h addr ha := h addr ha

/-- `Memory.read a` satisfies `RWConfined R W s₁` whenever `R a`. -/
theorem read_prog {R W : ℕ → Prop} {s₁ : Memory.State} {a : ℕ} (ha : R a) :
    RWConfined R W s₁ (Memory.read a) where
  fr₁ := rfl
  out₁ _ _ := rfl
  out₂ _ _ := ⟨rfl, fun _ _ => rfl⟩
  res_eq _ h := h a ha
  mem_in _ h addr hb := h addr hb

/-- `Memory.write a v` satisfies `RWConfined R W s₁` whenever `W a`. -/
theorem write_prog {R W : ℕ → Prop} {s₁ : Memory.State} {a : ℕ} (ha : W a) (v : ℕ) :
    RWConfined R W s₁ (Memory.write a v) where
  fr₁ := rfl
  out₁ addr hnot := by
    change Function.update s₁.mem a v addr = s₁.mem addr
    exact Function.update_of_ne (fun heq : addr = a => hnot (heq ▸ ha)) v s₁.mem
  out₂ s₂ _ := ⟨rfl, fun addr hnot => by
    change Function.update s₂.mem a v addr = s₂.mem addr
    exact Function.update_of_ne (fun heq : addr = a => hnot (heq ▸ ha)) v s₂.mem⟩
  res_eq _ _ := rfl
  mem_in s₂ h addr hb := by
    change Function.update s₁.mem a v addr = Function.update s₂.mem a v addr
    by_cases heq : addr = a
    · subst heq; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne heq, Function.update_of_ne heq, h addr hb]

/-- Lift a state-free `ConfinedTo M p` into `RWConfined R W s₁ p` when `M ⊆ W` and `M ⊆ R`. -/
theorem of_confined {α : Type} {M R W : ℕ → Prop} {s₁ : Memory.State} {p : Memory.Prog α}
    (hp : ConfinedTo M p) (hMW : ∀ addr, M addr → W addr) (hMR : ∀ addr, M addr → R addr) :
    RWConfined R W s₁ p where
  fr₁ := hp.fr_eq s₁
  out₁ addr hnot := hp.mem_out s₁ addr (fun hm => hnot (hMW addr hm))
  out₂ s₂ _ := ⟨hp.fr_eq s₂, fun addr hnot => hp.mem_out s₂ addr (fun hm => hnot (hMW addr hm))⟩
  res_eq s₂ h := hp.res_eq s₁ s₂ (fun addr hm => h addr (hMR addr hm))
  mem_in s₂ h addr ha := by
    by_cases hm : M addr
    · exact hp.mem_in s₁ s₂ (fun b hb => h b (hMR b hb)) addr hm
    · exact (hp.mem_out s₁ addr hm).trans ((h addr ha).trans (hp.mem_out s₂ addr hm).symm)

/-- Lift a read-only program `p` (`clientState s p = s`) whose return value depends only on `R`. -/
theorem of_readOnly {α : Type} {R W : ℕ → Prop} {s₁ : Memory.State} {p : Memory.Prog α}
    (hst : ∀ s, (Memory.spec 0).clientState s p = s)
    (hres : ∀ s₂, (∀ addr, R addr → s₁.mem addr = s₂.mem addr) →
      (Memory.spec 0).clientResult s₁ p = (Memory.spec 0).clientResult s₂ p) :
    RWConfined R W s₁ p where
  fr₁ := by rw [hst]
  out₁ _ _ := by rw [hst]
  out₂ s₂ _ := ⟨by rw [hst], fun _ _ => by rw [hst]⟩
  res_eq := hres
  mem_in s₂ h addr ha := by rw [hst, hst]; exact h addr ha

/-- Enlarge `(R₁, W₁)` to `(R₂, W₂)` when `W₁ ⊆ R₁`, `R₁ ⊆ R₂`, and `W₁ ⊆ W₂`. -/
theorem mono {α : Type} {R₁ W₁ R₂ W₂ : ℕ → Prop} {s₁ : Memory.State} {p : Memory.Prog α}
    (hp : RWConfined R₁ W₁ s₁ p)
    (hWR₁ : ∀ addr, W₁ addr → R₁ addr)
    (hR : ∀ addr, R₁ addr → R₂ addr)
    (hW : ∀ addr, W₁ addr → W₂ addr) :
    RWConfined R₂ W₂ s₁ p where
  fr₁ := hp.fr₁
  out₁ addr hnot := hp.out₁ addr (fun hw => hnot (hW addr hw))
  out₂ s₂ h :=
    let ho := hp.out₂ s₂ (fun addr ha => h addr (hR addr ha))
    ⟨ho.1, fun addr hnot => ho.2 addr (fun hw => hnot (hW addr hw))⟩
  res_eq s₂ h := hp.res_eq s₂ (fun addr ha => h addr (hR addr ha))
  mem_in s₂ h addr ha := by
    have hsub : ∀ b, R₁ b → s₁.mem b = s₂.mem b := fun b hb => h b (hR b hb)
    by_cases h1 : R₁ addr
    · exact hp.mem_in s₂ hsub addr h1
    · have hnw : ¬W₁ addr := fun hw => h1 (hWR₁ addr hw)
      exact (hp.out₁ addr hnw).trans ((h addr ha).trans ((hp.out₂ s₂ hsub).2 addr hnw).symm)

/-- Monadic bind (`>>=`) composition for `RWConfined`. -/
theorem bind_prog {α β : Type} {R W : ℕ → Prop} {s₁ : Memory.State}
    {p : Memory.Prog α} {q : α → Memory.Prog β}
    (hp : RWConfined R W s₁ p)
    (hq : RWConfined R W ((Memory.spec 0).clientState s₁ p)
      (q ((Memory.spec 0).clientResult s₁ p))) :
    RWConfined R W s₁ (p >>= q) where
  fr₁ := by
    rw [StateTransitionSpec.clientState_bind]
    exact hq.fr₁.trans hp.fr₁
  out₁ addr hnot := by
    rw [StateTransitionSpec.clientState_bind]
    exact (hq.out₁ addr hnot).trans (hp.out₁ addr hnot)
  out₂ s₂ h := by
    obtain ⟨hfr_p, hout_p⟩ := hp.out₂ s₂ h
    obtain ⟨hfr_q, hout_q⟩ := hq.out₂ ((Memory.spec 0).clientState s₂ p) (hp.mem_in s₂ h)
    have hres := hp.res_eq s₂ h
    refine ⟨?_, fun addr hnot => ?_⟩
    · rw [StateTransitionSpec.clientState_bind, ← hres]
      exact hfr_q.trans hfr_p
    · rw [StateTransitionSpec.clientState_bind, ← hres]
      exact (hout_q addr hnot).trans (hout_p addr hnot)
  res_eq s₂ h := by
    rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_bind,
      ← hp.res_eq s₂ h]
    exact hq.res_eq _ (hp.mem_in s₂ h)
  mem_in s₂ h addr ha := by
    rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
      ← hp.res_eq s₂ h]
    exact hq.mem_in _ (hp.mem_in s₂ h) addr ha

/-- Bind combinator for a read-only prefix on `s₁` (`clientState s₁ p = s₁`). -/
theorem bind_readOnly {α β : Type} {R W : ℕ → Prop} {s₁ : Memory.State}
    {p : Memory.Prog α} {q : α → Memory.Prog β}
    (hp : RWConfined R W s₁ p)
    (hst₁ : (Memory.spec 0).clientState s₁ p = s₁)
    (hq : RWConfined R W s₁ (q ((Memory.spec 0).clientResult s₁ p))) :
    RWConfined R W s₁ (p >>= q) :=
  bind_prog hp (by rw [hst₁]; exact hq)

/-- Bind combinator for a read-only prefix on `s₁` with known return value `r₀`. -/
theorem bind_readOnly_eq {α β : Type} {R W : ℕ → Prop} {s₁ : Memory.State}
    {p : Memory.Prog α} {r₀ : α} {q : α → Memory.Prog β}
    (hp : RWConfined R W s₁ p)
    (hst₁ : (Memory.spec 0).clientState s₁ p = s₁)
    (hres₁ : (Memory.spec 0).clientResult s₁ p = r₀)
    (hq : RWConfined R W s₁ (q r₀)) :
    RWConfined R W s₁ (p >>= q) :=
  bind_prog hp (by rw [hst₁, hres₁]; exact hq)

/-- Conditional (`if-then-else`) composition for `RWConfined`. -/
theorem ite_prog {α : Type} {R W : ℕ → Prop} {s₁ : Memory.State}
    {P : Prop} [Decidable P] {p₁ p₂ : Memory.Prog α}
    (h₁ : P → RWConfined R W s₁ p₁) (h₂ : ¬P → RWConfined R W s₁ p₂) :
    RWConfined R W s₁ (if P then p₁ else p₂) := by
  by_cases hP : P
  · rw [ite_eq_left hP]; exact h₁ hP
  · rw [ite_eq_right hP]; exact h₂ hP

/-- Transport full agreement on an ambient region `M` (`W ⊆ R ⊆ M`) across an `RWConfined` step. -/
theorem step_agree {α : Type} {R W M : ℕ → Prop} {s₁ s₂ : Memory.State} {p : Memory.Prog α}
    (hp : RWConfined R W s₁ p)
    (hWR : ∀ addr, W addr → R addr)
    (hRM : ∀ addr, R addr → M addr)
    (hfr : s₁.frontier = s₂.frontier)
    (hmem : ∀ addr, M addr → s₁.mem addr = s₂.mem addr) :
    (Memory.spec 0).clientResult s₁ p = (Memory.spec 0).clientResult s₂ p ∧
    ((Memory.spec 0).clientState s₁ p).frontier =
      ((Memory.spec 0).clientState s₂ p).frontier ∧
    (∀ addr, M addr →
      ((Memory.spec 0).clientState s₁ p).mem addr =
        ((Memory.spec 0).clientState s₂ p).mem addr) := by
  have hmemR : ∀ addr, R addr → s₁.mem addr = s₂.mem addr :=
    fun addr ha => hmem addr (hRM addr ha)
  obtain ⟨hfr₂, hout₂⟩ := hp.out₂ s₂ hmemR
  refine ⟨hp.res_eq s₂ hmemR, hp.fr₁.trans (hfr.trans hfr₂.symm), fun addr hm => ?_⟩
  by_cases hr : R addr
  · exact hp.mem_in s₂ hmemR addr hr
  · have hnw : ¬W addr := fun hw => hr (hWR addr hw)
    exact (hp.out₁ addr hnw).trans ((hmem addr hm).trans (hout₂ addr hnw).symm)

end RWConfined

/-- Lift `RWConfined R W s₁ p` (`W ⊆ R ⊆ M`) into `SlotCoupledStep M io n s₁ s₂ p`. -/
theorem SlotCoupledStep.of_rwConfined {α : Type} {M R W : ℕ → Prop} {io : SlotIoLayout} {n : ℕ}
    {s₁ s₂ : Memory.State} {p : Memory.Prog α}
    (hc : SlotStateCoupled M io n s₁ s₂)
    (hp : RWConfined R W s₁ p)
    (hWR : ∀ addr, W addr → R addr)
    (hRM : ∀ addr, R addr → M addr) :
    SlotCoupledStep M io n s₁ s₂ p := by
  have hw := hc.valid₁.w_pos
  have hmemR : ∀ addr, R addr → s₁.mem addr = s₂.mem addr :=
    fun addr ha => hc.mem_eq addr (hRM addr ha)
  obtain ⟨hres, hfr', hmemM'⟩ := hp.step_agree hWR hRM hc.fr_eq hc.mem_eq
  obtain ⟨_, hout₂⟩ := hp.out₂ s₂ hmemR
  have hnw_io : ∀ addr, io.OwnsAddr addr → ¬W addr :=
    fun addr hia hw_a => hc.disj addr (hRM addr (hWR addr hw_a)) hia
  obtain ⟨hinv₁', harr₁'⟩ := io.congr_of_outside hw hc.inv₁
    (fun addr hia => hp.out₁ addr (hnw_io addr hia))
  obtain ⟨hinv₂', harr₂'⟩ := io.congr_of_outside hw hc.inv₂
    (fun addr hia => hout₂ addr (hnw_io addr hia))
  exact ⟨hres, {
    fr_eq := hfr'
    side_zero := hc.side_zero
    valid₁ := hp.fr₁.symm ▸ hc.valid₁
    disj := hc.disj
    mem_eq := hmemM'
    inv₁ := hinv₁'
    inv₂ := hinv₂'
    pair_eq := fun idx hidx =>
      (harr₁' idx hidx).trans ((hc.pair_eq idx hidx).trans (harr₂' idx hidx).symm)
  }⟩

/-! ## Section 2: `FastEpochLayout` Regions, `FastTableReady`, and Primitive `RWConfined` -/

/-- Metadata-only write region of `fl` (excluding `metaBase + 0`, seeds, `pBase`, and `io`). -/
private def FastWriteMeta (fl : FastEpochLayout) (addr : ℕ) : Prop :=
  (fl.metaBase + 1 ≤ addr ∧ addr < fl.metaBase + 18) ∨
  (fl.metaBase + offBktMeta fl.c fl.w fl.N ≤ addr ∧
    addr < fl.metaBase + offPageDir fl.c fl.w fl.N)

/-- Metadata + hash-seed + `pBase` read region of `fl` (disjoint from `fl.io.OwnsAddr`). -/
private def FastReadMeta (fl : FastEpochLayout) (addr : ℕ) : Prop :=
  (fl.pBase ≤ addr ∧ addr < fl.pBase + 64) ∨
  (fl.metaBase ≤ addr ∧ addr < fl.metaBase + 18) ∨
  (fl.metaBase + 32 ≤ addr ∧ addr < fl.metaBase + offPageDir fl.c fl.w fl.N)

/-- Direct-mode read/write envelope of `fl` (`FastReadMeta` union `fl.io.OwnsAddr`). -/
private def FastReadDirect (fl : FastEpochLayout) (addr : ℕ) : Prop :=
  FastReadMeta fl addr ∨ fl.io.OwnsAddr addr

/-- Static layout + `ParamTable` bundle preserved automatically by any `FastWriteMeta` or
`OwnsFastAddr` step. -/
private structure FastTableReady (w : ℕ) (fl : FastEpochLayout) (s : Memory.State) : Prop where
  valid : fl.Valid w s.frontier
  pt : fl.ParamTable s.mem

private theorem FastTableReady.of_ready {w : ℕ} {fl : FastEpochLayout} {s : Memory.State}
    (hr : FastLayoutReady w fl s) : FastTableReady w fl s := by
  obtain ⟨hv, hpt, _⟩ := hr
  exact ⟨hv, hpt⟩

private theorem writeMeta_sub_readMeta {fl : FastEpochLayout} (addr : ℕ)
    (hw : FastWriteMeta fl addr) : FastReadMeta fl addr := by
  rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inr (Or.inl ⟨by omega, h2⟩)
  · refine Or.inr (Or.inr ⟨?_, h2⟩)
    unfold offBktMeta offFpHash offBktHash at h1
    omega

private theorem writeMeta_sub_ownsFast {fl : FastEpochLayout} (addr : ℕ)
    (hw : FastWriteMeta fl addr) : fl.OwnsFastAddr addr := by
  rcases hw with h1 | h2
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)

private theorem ownsFast_sub_readDirect {fl : FastEpochLayout} (addr : ℕ)
    (hw : fl.OwnsFastAddr addr) : FastReadDirect fl addr := by
  rcases hw with h1 | h2 | hio
  · exact Or.inl (writeMeta_sub_readMeta addr (Or.inl h1))
  · exact Or.inl (writeMeta_sub_readMeta addr (Or.inr h2))
  · exact Or.inr hio

private theorem FastTableReady.step_meta {α : Type} {w : ℕ} {fl : FastEpochLayout}
    {s : Memory.State} {p : Memory.Prog α}
    (htr : FastTableReady w fl s)
    (hp : RWConfined (FastReadMeta fl) (FastWriteMeta fl) s p) :
    FastTableReady w fl ((Memory.spec 0).clientState s p) where
  valid := hp.fr₁.symm ▸ htr.valid
  pt := htr.pt.congr fun addr h1 h2 =>
    hp.out₁ addr (fun hw =>
      htr.valid.not_ownsFast_pBase h1 (by omega) (writeMeta_sub_ownsFast addr hw))

private theorem FastTableReady.step_direct {α : Type} {w : ℕ} {fl : FastEpochLayout}
    {s : Memory.State} {p : Memory.Prog α}
    (htr : FastTableReady w fl s)
    (hp : RWConfined (FastReadDirect fl) fl.OwnsFastAddr s p) :
    FastTableReady w fl ((Memory.spec 0).clientState s p) where
  valid := hp.fr₁.symm ▸ htr.valid
  pt := htr.pt.congr fun addr h1 h2 =>
    hp.out₁ addr (htr.valid.not_ownsFast_pBase h1 (by omega))

private theorem rw_meta_to_direct {α : Type} {fl : FastEpochLayout} {s : Memory.State}
    {p : Memory.Prog α}
    (hp : RWConfined (FastReadMeta fl) (FastWriteMeta fl) s p) :
    RWConfined (FastReadDirect fl) fl.OwnsFastAddr s p :=
  hp.mono writeMeta_sub_readMeta (fun _ => Or.inl) writeMeta_sub_ownsFast

/-- State-opaque monadic bind combinator for `FastWriteMeta` steps. -/
private theorem rw_bind_meta {α β : Type} {w : ℕ} {fl : FastEpochLayout} {s : Memory.State}
    {p : Memory.Prog α} {q : α → Memory.Prog β}
    (htr : FastTableReady w fl s)
    (hp : RWConfined (FastReadMeta fl) (FastWriteMeta fl) s p)
    (hq : ∀ s', FastTableReady w fl s' → ∀ r,
      RWConfined (FastReadMeta fl) (FastWriteMeta fl) s' (q r)) :
    RWConfined (FastReadMeta fl) (FastWriteMeta fl) s (p >>= q) :=
  RWConfined.bind_prog hp (hq _ (htr.step_meta hp) _)

/-- State-opaque monadic bind combinator for direct-mode `OwnsFastAddr` steps. -/
private theorem rw_bind_direct {α β : Type} {w : ℕ} {fl : FastEpochLayout} {s : Memory.State}
    {p : Memory.Prog α} {q : α → Memory.Prog β}
    (htr : FastTableReady w fl s)
    (hp : RWConfined (FastReadDirect fl) fl.OwnsFastAddr s p)
    (hq : ∀ s', FastTableReady w fl s' → ∀ r,
      RWConfined (FastReadDirect fl) fl.OwnsFastAddr s' (q r)) :
    RWConfined (FastReadDirect fl) fl.OwnsFastAddr s (p >>= q) :=
  RWConfined.bind_prog hp (hq _ (htr.step_direct hp) _)

private theorem pBase_in_readMeta {fl : FastEpochLayout} {k : ℕ} (hk : k < 64) :
    FastReadMeta fl (fl.pBase + k) :=
  Or.inl ⟨Nat.le_add_right _ _, by omega⟩

private theorem cf_readParamPair {fl : FastEpochLayout} {k₁ k₂ : ℕ}
    (hk₁ : k₁ < 64) (hk₂ : k₂ < 64) :
    ConfinedTo (FastReadMeta fl) (readParamPairProg (fl.pBase, (k₁, k₂))) := by
  unfold readParamPairProg
  exact ConfinedTo.bind_prog (ConfinedTo.read_prog (pBase_in_readMeta hk₁)) fun _ =>
    ConfinedTo.bind_prog (ConfinedTo.read_prog (pBase_in_readMeta hk₂)) fun _ =>
    ConfinedTo.pure_prog _

private theorem cf_readParamQuad {fl : FastEpochLayout} {k₁ k₂ k₃ k₄ : ℕ}
    (hk₁ : k₁ < 64) (hk₂ : k₂ < 64) (hk₃ : k₃ < 64) (hk₄ : k₄ < 64) :
    ConfinedTo (FastReadMeta fl) (readParamQuadProg ((fl.pBase, (k₁, k₂)), (k₃, k₄))) := by
  unfold readParamQuadProg
  exact ConfinedTo.bind_prog (cf_readParamPair hk₁ hk₂) fun _ =>
    ConfinedTo.bind_prog (cf_readParamPair hk₃ hk₄) fun _ =>
    ConfinedTo.pure_prog _

private theorem rw_readParam {R W : ℕ → Prop} {s : Memory.State} {a : ℕ}
    (ha : R a) : RWConfined R W s (Memory.read a) :=
  RWConfined.read_prog ha

private theorem rw_loadBpMetaCtx {w : ℕ} {fl : FastEpochLayout} {W : ℕ → Prop} {s : Memory.State}
    (_htr : FastTableReady w fl s) :
    RWConfined (FastReadMeta fl) W s (loadBpMetaCtxProg fl.pBase) := by
  have hcf : ConfinedTo (FastReadMeta fl) (loadBpMetaCtxProg fl.pBase) := by
    unfold loadBpMetaCtxProg
    exact ConfinedTo.bind_prog (cf_readParamQuad (by decide) (by decide) (by decide) (by decide))
      fun _ => ConfinedTo.bind_prog
        (cf_readParamQuad (by decide) (by decide) (by decide) (by decide)) fun _ =>
      ConfinedTo.bind_prog (cf_readParamQuad (by decide) (by decide) (by decide) (by decide))
        fun _ => ConfinedTo.bind_prog (cf_readParamPair (by decide) (by decide))
        fun _ => ConfinedTo.pure_prog _
  exact RWConfined.of_readOnly (clientState_loadBpMetaCtxProg fl.pBase) (hcf.res_eq s)

private theorem rw_loadSlotIoCtx {fl : FastEpochLayout} {W : ℕ → Prop} {s : Memory.State} :
    RWConfined (FastReadMeta fl) W s (loadSlotIoCtxProg fl.pBase) := by
  have hcf : ConfinedTo (FastReadMeta fl) (loadSlotIoCtxProg fl.pBase) := by
    unfold loadSlotIoCtxProg
    exact ConfinedTo.bind_prog (cf_readParamPair (by decide) (by decide)) fun _ =>
      ConfinedTo.bind_prog (cf_readParamQuad (by decide) (by decide) (by decide) (by decide))
        fun _ => ConfinedTo.bind_prog
          (cf_readParamQuad (by decide) (by decide) (by decide) (by decide)) fun _ =>
      ConfinedTo.bind_prog (cf_readParamPair (by decide) (by decide)) fun _ =>
      ConfinedTo.bind_prog (ConfinedTo.read_prog (pBase_in_readMeta (by decide))) fun _ =>
      ConfinedTo.pure_prog _
  exact RWConfined.of_readOnly (clientState_loadSlotIoCtxProg fl.pBase) (hcf.res_eq s)

private theorem rw_loadBlockPoolCtx {w : ℕ} {fl : FastEpochLayout} {W : ℕ → Prop}
    {s : Memory.State} (htr : FastTableReady w fl s) :
    RWConfined (FastReadMeta fl) W s (loadBlockPoolCtxProg fl.pBase) := by
  unfold loadBlockPoolCtxProg
  refine RWConfined.bind_readOnly (rw_loadBpMetaCtx htr) (clientState_loadBpMetaCtxProg _ s) ?_
  refine RWConfined.bind_readOnly rw_loadSlotIoCtx (clientState_loadSlotIoCtxProg _ s) ?_
  exact RWConfined.pure_prog _

private theorem rw_loadHashStaticCtx {fl : FastEpochLayout} {W : ℕ → Prop} {isFp : ℕ}
    {s : Memory.State} :
    RWConfined (FastReadMeta fl) W s (loadHashStaticCtxProg (fl.pBase, isFp)) := by
  have hcf : ConfinedTo (FastReadMeta fl) (loadHashStaticCtxProg (fl.pBase, isFp)) := by
    unfold loadHashStaticCtxProg; simp only [pure_bind]
    have hk1 : (if isFp = 0 then 61 else 62) < 64 := by split_ifs <;> decide
    have hk2 : (if isFp = 0 then 8 else 9) < 64 := by split_ifs <;> decide
    exact ConfinedTo.bind_prog (cf_readParamQuad hk1 (by decide) (by decide) (by decide)) fun _ =>
      ConfinedTo.bind_prog (cf_readParamPair (by decide) (by decide)) fun _ =>
      ConfinedTo.bind_prog (ConfinedTo.read_prog (pBase_in_readMeta (by decide))) fun _ =>
      ConfinedTo.bind_prog (cf_readParamPair (by decide) hk2) fun _ => ConfinedTo.pure_prog _
  exact RWConfined.of_readOnly (clientState_loadHashStaticCtxProg _) (hcf.res_eq s)

private theorem rw_loadTrieCtx {fl : FastEpochLayout} {W : ℕ → Prop} {role : ℕ}
    {s : Memory.State} :
    RWConfined (FastReadMeta fl) W s (loadTrieCtxProg (fl.pBase, role)) := by
  have hcf : ConfinedTo (FastReadMeta fl) (loadTrieCtxProg (fl.pBase, role)) := by
    unfold loadTrieCtxProg; simp only [pure_bind]
    have hk1 : (if role = 0 then 39 else 40) < 64 := by split_ifs <;> decide
    have hk2 : (if role = 0 then 41 else 42) < 64 := by split_ifs <;> decide
    have hk3 : (if role = 0 then 43 else 44) < 64 := by split_ifs <;> decide
    exact ConfinedTo.bind_prog (cf_readParamQuad (by decide) hk1 hk2 hk3) fun _ =>
      ConfinedTo.bind_prog (cf_readParamPair (by decide) (by decide)) fun _ =>
      ConfinedTo.bind_prog (cf_readParamQuad (by decide) (by decide) (by decide) (by decide))
        fun _ => ConfinedTo.pure_prog _
  exact RWConfined.of_readOnly (clientState_loadTrieCtxProg _) (hcf.res_eq s)

private theorem rw_loadBTreeSliceCtx {fl : FastEpochLayout} {W : ℕ → Prop} {b role : ℕ}
    {s : Memory.State} :
    RWConfined (FastReadMeta fl) W s (loadBTreeSliceCtxProg (fl.pBase, (b, role))) := by
  have hcf : ConfinedTo (FastReadMeta fl) (loadBTreeSliceCtxProg (fl.pBase, (b, role))) := by
    unfold loadBTreeSliceCtxProg
    exact ConfinedTo.bind_prog (cf_readParamPair (by decide) (by decide)) fun _ =>
      ConfinedTo.bind_prog (ConfinedTo.read_prog (pBase_in_readMeta (by decide))) fun _ =>
      ConfinedTo.bind_prog (cf_readParamPair (by decide) (by decide)) fun _ =>
      ConfinedTo.bind_prog (cf_readParamPair (by decide) (by decide)) fun _ =>
      ConfinedTo.bind_prog (ConfinedTo.read_prog (pBase_in_readMeta (by decide))) fun _ =>
      ConfinedTo.bind_prog (cf_readParamPair (by decide) (by decide)) fun _ =>
      ConfinedTo.bind_prog (cf_readParamQuad (by decide) (by decide) (by decide) (by decide))
        fun _ =>
      ConfinedTo.bind_prog (ConfinedTo.read_prog (pBase_in_readMeta (by decide))) fun _ =>
      ConfinedTo.pure_prog _
  exact RWConfined.of_readOnly (clientState_loadBTreeSliceCtxProg _) (hcf.res_eq s)

private theorem bpMetaConf_fast {w : ℕ} {fl : FastEpochLayout} {fr : ℕ} (hv : fl.Valid w fr) :
    BpMetaConf (FastWriteMeta fl) fl.mp.toCtx := by
  have hmv := hv.mp_valid
  dsimp only [BpMetaConf]
  rw [BpMetaLayout.ofCtx_toCtx]
  refine ⟨hmv.w_pos, hmv.sixteen_MK_le_maxTail, fun addr hma => ?_⟩
  rcases BpMetaLayout.OwnsMetaAddr.bounds hmv hma with (rfl | ⟨h10, h17⟩) | ⟨hlo, hhi⟩
  · exact Or.inl ⟨by dsimp [FastEpochLayout.mp, epochBpMetaLayout]; omega,
      by dsimp [FastEpochLayout.mp, epochBpMetaLayout]; omega⟩
  · exact Or.inl ⟨by dsimp [FastEpochLayout.mp, epochBpMetaLayout] at *; omega,
      by dsimp [FastEpochLayout.mp, epochBpMetaLayout] at *; omega⟩
  · refine Or.inr ⟨hlo, ?_⟩
    dsimp only [FastEpochLayout.mp, epochBpMetaLayout] at hhi
    unfold offPageDir offTrieItem offTrieNode offTrieChild offBTreeVals offBTreeKeys offBTreeMeta
    omega

private theorem feistelConf_bkt {w : ℕ} {fl : FastEpochLayout} {fr : ℕ} (hv : fl.Valid w fr) :
    FeistelConf (FastReadMeta fl) fl.feistelCtx := by
  refine ⟨hv.w_eq ▸ hv.w_pos, rfl, fun addr hlo hhi => Or.inr (Or.inr ⟨?_, ?_⟩)⟩
  · dsimp only [FastEpochLayout.bktHashBase] at hlo
    unfold offBktHash at hlo; omega
  · dsimp only [FastEpochLayout.bktHashBase] at hhi
    unfold offPageDir offTrieItem offTrieNode offTrieChild offBTreeVals offBTreeKeys offBTreeMeta
      offTailOwner offSlabOwner offTailDir offSlabDir offBktMeta offFpHash offBktHash
    unfold offBktHash at hhi
    omega

private theorem feistelConf_fp {w : ℕ} {fl : FastEpochLayout} {fr : ℕ} (hv : fl.Valid w fr) :
    FeistelConf (FastReadMeta fl) fl.fpStaticCtx := by
  refine ⟨hv.w_eq ▸ hv.w_pos, rfl, fun addr hlo hhi => Or.inr (Or.inr ⟨?_, ?_⟩)⟩
  · dsimp only [FastEpochLayout.fpHashBase] at hlo
    unfold offFpHash offBktHash at hlo; omega
  · dsimp only [FastEpochLayout.fpHashBase] at hhi
    unfold offPageDir offTrieItem offTrieNode offTrieChild offBTreeVals offBTreeKeys offBTreeMeta
      offTailOwner offSlabOwner offTailDir offSlabDir offBktMeta
    omega

private theorem trieConf_fast {w : ℕ} {fl : FastEpochLayout} {fr role : ℕ}
    (hv : fl.Valid w fr) (hrole : role < 2) :
    TrieConf (FastWriteMeta fl) (fl.trieL role).toCtx := by
  have htv := hv.trie_valid hrole
  obtain ⟨_, _, _, _, _, _, hmn1, _, _, _, _, _, _, hcn, hni, _⟩ := htv
  dsimp only [TrieConf]
  rw [TrieLayout.ofCtx_toCtx]
  refine ⟨by dsimp [FastEpochLayout.trieL, epochTrieLayout]; exact hv.w_eq ▸ hv.w_pos,
    hmn1, fun addr ha => ?_⟩
  dsimp only [FastEpochLayout.trieL, epochTrieLayout, TrieLayout.OwnsAddr] at ha hcn hni
  refine Or.inr ⟨?_, ?_⟩
  · rcases role with _ | _ | _ <;> try omega
    all_goals (
      unfold offTrieItem offTrieNode offTrieChild at ha
      rcases ha with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ <;>
        (unfold offBTreeVals offBTreeKeys offBTreeMeta offTailOwner offSlabOwner
           offTailDir offSlabDir at h1; omega))
  · rcases role with _ | _ | _ <;> try omega
    all_goals (
      unfold offTrieItem offTrieNode offTrieChild trieItemWords trieNodeWords trieChildWords at ha
      unfold offPageDir offTrieItem offTrieNode offTrieChild trieItemWords trieNodeWords
        trieChildWords
      rcases ha with ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩ <;> omega)

private theorem btreeSliceConf_fast {w : ℕ} {fl : FastEpochLayout} {fr b role : ℕ}
    (hv : fl.Valid w fr) (hb : b < numBucketsWhp fl.N) (hrole : role < 3) :
    BTreeSliceConf (FastWriteMeta fl) (fl.btL.toSliceCtx b role) := by
  have h64 := sixty_four_le_nSliceWhp fl.N
  dsimp only [BTreeSliceConf]
  rw [unpackSliceCtx_toSliceCtx]
  refine ⟨by dsimp [FastEpochLayout.btL, epochBTreeLayout]; exact hv.w_eq ▸ hv.w_pos,
    by dsimp [FastEpochLayout.btL, epochBTreeLayout]; omega,
    hb, hrole, fun addr ha => Or.inr ⟨?_, ?_⟩⟩
  · dsimp only [FastEpochLayout.btL, epochBTreeLayout, BTreeEpochLayout.OwnsAddr] at ha
    rcases ha with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩
    · exact h1
    · unfold offBTreeMeta offTailOwner offSlabOwner offTailDir offSlabDir at h1; omega
    · unfold offBTreeKeys offBTreeMeta offTailOwner offSlabOwner offTailDir offSlabDir at h1; omega
    · unfold offBTreeVals offBTreeKeys offBTreeMeta offTailOwner offSlabOwner offTailDir
        offSlabDir at h1
      omega
  · dsimp only [FastEpochLayout.btL, epochBTreeLayout, BTreeEpochLayout.OwnsAddr,
      BTreeEpochLayout.totalNodes] at ha
    unfold offBTreeVals offBTreeKeys offBTreeMeta offTailOwner offSlabOwner
      offTailDir offSlabDir at ha
    unfold offPageDir offTrieItem offTrieNode offTrieChild offBTreeVals offBTreeKeys
      offBTreeMeta offTailOwner offSlabOwner offTailDir offSlabDir
    dsimp only [totalBTreeNodesWhp] at ha ⊢
    rcases ha with ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩ <;> omega

private theorem rw_fastFeistelSplit {w : ℕ} {fl : FastEpochLayout} {u_val : ℕ}
    {s : Memory.State} (htr : FastTableReady w fl s) :
    RWConfined (FastReadMeta fl) (FastWriteMeta fl) s (fastFeistelSplitProg (fl.pBase, u_val)) := by
  unfold fastFeistelSplitProg
  refine RWConfined.bind_readOnly (rw_readParam (pBase_in_readMeta (by decide))) rfl ?_
  refine RWConfined.ite_prog (fun _ => ?_) (fun _ => RWConfined.pure_prog _)
  refine RWConfined.bind_readOnly_eq rw_loadHashStaticCtx
    (clientState_loadHashStaticCtxProg _ s) (clientResult_loadFeistelCtx htr.pt) ?_
  have hcf := confinedTo_feistelSplitBoundedProg (u_val := u_val) (feistelConf_bkt htr.valid)
  exact RWConfined.of_readOnly (fun st => by
    unfold feistelSplitBoundedProg; dsimp only [FastEpochLayout.feistelCtx]; simp only [pure_bind]
    rw [StateTransitionSpec.clientState_bind, clientState_evalSaltedBoundedProg]; rfl)
    (hcf.res_eq s)

private theorem rw_fastFeistelRecon {w : ℕ} {fl : FastEpochLayout} {bkt q_val : ℕ}
    {s : Memory.State} (htr : FastTableReady w fl s) :
    RWConfined (FastReadMeta fl) (FastWriteMeta fl) s
      (fastFeistelReconProg (fl.pBase, (bkt, q_val))) := by
  unfold fastFeistelReconProg
  refine RWConfined.bind_readOnly_eq rw_loadHashStaticCtx
    (clientState_loadHashStaticCtxProg _ s) (clientResult_loadFeistelCtx htr.pt) ?_
  dsimp only [FastEpochLayout.feistelCtx]
  refine RWConfined.ite_prog (fun _ => ?_) (fun _ => RWConfined.pure_prog _)
  simp only [pure_bind]
  refine RWConfined.ite_prog (fun _ => RWConfined.ite_prog (fun _ => ?_)
    (fun _ => RWConfined.pure_prog _)) (fun _ => RWConfined.pure_prog _)
  have hcf := confinedTo_feistelReconBoundedProg (bkt := bkt) (q_val := q_val)
    (feistelConf_bkt htr.valid)
  exact RWConfined.of_readOnly (fun st => by
    unfold feistelReconBoundedProg; dsimp only [FastEpochLayout.feistelCtx]; simp only [pure_bind]
    rw [StateTransitionSpec.clientState_bind, clientState_evalSaltedBoundedProg]; rfl)
    (hcf.res_eq s)

private theorem rw_fastRKey {w : ℕ} {fl : FastEpochLayout} {u_val : ℕ}
    {s : Memory.State} (htr : FastTableReady w fl s) :
    RWConfined (FastReadMeta fl) (FastWriteMeta fl) s (fastRKeyProg (fl.pBase, u_val)) := by
  unfold fastRKeyProg
  refine RWConfined.bind_readOnly (rw_readParam (pBase_in_readMeta (by decide))) rfl ?_
  refine RWConfined.ite_prog (fun _ => ?_) (fun _ => RWConfined.pure_prog _)
  have h62 : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 62)) = fl.fpHashBase :=
    htr.pt 62 (by decide)
  refine RWConfined.bind_readOnly_eq (rw_readParam (pBase_in_readMeta (by decide))) rfl h62 ?_
  have hpair : RWConfined (FastReadMeta fl) (FastWriteMeta fl) s
      (readParamPairProg (fl.pBase, (3, 4))) :=
    RWConfined.of_readOnly (fun _ => rfl) ((cf_readParamPair (by decide) (by decide)).res_eq s)
  refine RWConfined.bind_readOnly hpair rfl ?_
  have hfp_in : FastReadMeta fl fl.fpHashBase := by
    have hsp := BitPackedDoubleTabulation.space_pos fl.w (cTabWhp fl.c) (dTabWhp fl.c)
      (bCharWhp fl.N) (fpBitsWhp fl.N)
    refine Or.inr (Or.inr ⟨?_, ?_⟩)
    · dsimp only [FastEpochLayout.fpHashBase]; unfold offFpHash offBktHash; omega
    · dsimp only [FastEpochLayout.fpHashBase]
      unfold offPageDir offTrieItem offTrieNode offTrieChild offBTreeVals offBTreeKeys
        offBTreeMeta offTailOwner offSlabOwner offTailDir offSlabDir offBktMeta
      omega
  refine RWConfined.bind_readOnly (rw_readParam hfp_in) rfl ?_
  exact RWConfined.of_readOnly (clientState_oddMulReducedProg _)
    ((confinedTo_oddMulReducedProg (FastReadMeta fl) _).res_eq s)

private theorem rw_fastFpHash {w : ℕ} {fl : FastEpochLayout} {salt u_val : ℕ}
    {s : Memory.State} (htr : FastTableReady w fl s) :
    RWConfined (FastReadMeta fl) (FastWriteMeta fl) s
      (fastFpHashProg (fl.pBase, (salt, u_val))) := by
  unfold fastFpHashProg
  refine RWConfined.bind_readOnly (rw_readParam (pBase_in_readMeta (by decide))) rfl ?_
  have h24 : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 24)) =
      sMaxWhp fl.c fl.N := htr.pt 24 (by decide)
  refine RWConfined.bind_readOnly_eq (rw_readParam (pBase_in_readMeta (by decide))) rfl h24 ?_
  refine RWConfined.ite_prog (fun _ => RWConfined.ite_prog (fun hsalt => ?_)
    (fun _ => RWConfined.pure_prog _)) (fun _ => RWConfined.pure_prog _)
  refine RWConfined.bind_readOnly_eq rw_loadHashStaticCtx
    (clientState_loadHashStaticCtxProg _ s) (clientResult_loadFpStaticCtx htr.pt) ?_
  have hs_pow : salt < 2 ^ bCharWhp fl.N :=
    lt_of_lt_of_le hsalt (sMaxWhp_le_two_pow_bCharWhp htr.valid.thresh_le)
  have hcf := confinedTo_evalSaltedBoundedProg (u_val := u_val) (feistelConf_fp htr.valid) hs_pow
  exact RWConfined.of_readOnly (clientState_evalSaltedBoundedProg _) (hcf.res_eq s)

private theorem rw_fastReadMeta {w : ℕ} {fl : FastEpochLayout} {off : ℕ}
    {s : Memory.State} (htr : FastTableReady w fl s) :
    RWConfined (FastReadMeta fl) (FastWriteMeta fl) s (fastReadMetaProg (fl.pBase, off)) := by
  unfold fastReadMetaProg
  refine RWConfined.ite_prog (fun hoff => ?_) (fun _ => RWConfined.pure_prog _)
  have h1 : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 1)) = fl.metaBase :=
    htr.pt 1 (by decide)
  refine RWConfined.bind_readOnly_eq (rw_readParam (pBase_in_readMeta (by decide))) rfl h1 ?_
  exact rw_readParam (Or.inr (Or.inl ⟨Nat.le_add_right _ _, by omega⟩))

private theorem rw_fastWriteMeta {w : ℕ} {fl : FastEpochLayout} {off val : ℕ}
    {s : Memory.State} (htr : FastTableReady w fl s) :
    RWConfined (FastReadMeta fl) (FastWriteMeta fl) s
      (fastWriteMetaProg ((fl.pBase, off), val)) := by
  unfold fastWriteMetaProg
  refine RWConfined.ite_prog (fun hoff => ?_) (fun _ => RWConfined.pure_prog _)
  have h1 : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 1)) = fl.metaBase :=
    htr.pt 1 (by decide)
  refine RWConfined.bind_readOnly_eq (rw_readParam (pBase_in_readMeta (by decide))) rfl h1 ?_
  exact RWConfined.write_prog (Or.inl ⟨by omega, by omega⟩) val

private theorem rw_fastReadBktLane {w : ℕ} {fl : FastEpochLayout} {b lane : ℕ}
    {s : Memory.State} (htr : FastTableReady w fl s) :
    RWConfined (FastReadMeta fl) (FastWriteMeta fl) s
      (fastReadBktLaneProg (fl.pBase, (b, lane))) := by
  unfold fastReadBktLaneProg
  have h11 : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 11)) =
      numBucketsWhp fl.N := htr.pt 11 (by decide)
  refine RWConfined.bind_readOnly_eq (rw_readParam (pBase_in_readMeta (by decide))) rfl h11 ?_
  refine RWConfined.ite_prog (fun ⟨hb, hl⟩ => ?_) (fun _ => RWConfined.pure_prog _)
  have h1 : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 1)) = fl.metaBase :=
    htr.pt 1 (by decide)
  have h31 : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 31)) =
      offBktMeta fl.c fl.w fl.N := htr.pt 31 (by decide)
  have hpbw : (Memory.spec 0).clientResult s (readParamPairProg (fl.pBase, (10, 2))) =
      (globalPtrBits fl.N, fl.w) := by
    unfold readParamPairProg
    simp [StateTransitionSpec.clientResult, htr.pt 10 (by decide), htr.pt 2 (by decide),
      FastEpochLayout.paramWord]
  refine RWConfined.bind_readOnly_eq (rw_readParam (pBase_in_readMeta (by decide))) rfl h1 ?_
  refine RWConfined.bind_readOnly_eq (rw_readParam (pBase_in_readMeta (by decide))) rfl h31 ?_
  refine RWConfined.bind_readOnly_eq
    (RWConfined.of_readOnly (fun _ => rfl) ((cf_readParamPair (by decide) (by decide)).res_eq s))
    rfl hpbw ?_
  obtain ⟨_, _, hbmM⟩ := bpMetaConf_fast htr.valid
  have hcf : ConfinedTo (FastWriteMeta fl)
      (readPackedCompGenProg (((fl.metaBase, offBktMeta fl.c fl.w fl.N),
        (globalPtrBits fl.N, fl.w)), 16 * b + lane)) :=
    ConfinedTo.readPackedComp_prog (htr.valid.w_eq ▸ htr.valid.w_pos)
      (nMax := 16 * numBucketsWhp fl.N) (by omega)
      fun addr ha1 ha2 => hbmM addr (by
        rw [BpMetaLayout.ofCtx_toCtx]
        exact Or.inr (Or.inr (Or.inl ⟨ha1, ha2⟩)))
  exact RWConfined.of_confined hcf (fun _ h => h) writeMeta_sub_readMeta

private theorem rw_fastWriteBktLane {w : ℕ} {fl : FastEpochLayout} {b lane val : ℕ}
    {s : Memory.State} (htr : FastTableReady w fl s) :
    RWConfined (FastReadMeta fl) (FastWriteMeta fl) s
      (fastWriteBktLaneProg ((fl.pBase, (b, lane)), val)) := by
  unfold fastWriteBktLaneProg
  have h11 : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 11)) =
      numBucketsWhp fl.N := htr.pt 11 (by decide)
  refine RWConfined.bind_readOnly_eq (rw_readParam (pBase_in_readMeta (by decide))) rfl h11 ?_
  refine RWConfined.bind_readOnly (rw_readParam (pBase_in_readMeta (by decide))) rfl ?_
  refine RWConfined.ite_prog (fun ⟨hb, hl, _⟩ => ?_) (fun _ => RWConfined.pure_prog _)
  have h1 : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 1)) = fl.metaBase :=
    htr.pt 1 (by decide)
  have h31 : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 31)) =
      offBktMeta fl.c fl.w fl.N := htr.pt 31 (by decide)
  have hpbw : (Memory.spec 0).clientResult s (readParamPairProg (fl.pBase, (10, 2))) =
      (globalPtrBits fl.N, fl.w) := by
    unfold readParamPairProg
    simp [StateTransitionSpec.clientResult, htr.pt 10 (by decide), htr.pt 2 (by decide),
      FastEpochLayout.paramWord]
  have hl_lt : lane < 16 := by omega
  refine RWConfined.bind_readOnly_eq (rw_readParam (pBase_in_readMeta (by decide))) rfl h1 ?_
  refine RWConfined.bind_readOnly_eq (rw_readParam (pBase_in_readMeta (by decide))) rfl h31 ?_
  refine RWConfined.bind_readOnly_eq
    (RWConfined.of_readOnly (fun _ => rfl) ((cf_readParamPair (by decide) (by decide)).res_eq s))
    rfl hpbw ?_
  obtain ⟨_, _, hbmM⟩ := bpMetaConf_fast htr.valid
  have hcf : ConfinedTo (FastWriteMeta fl)
      (writePackedCompGenProg ((((fl.metaBase, offBktMeta fl.c fl.w fl.N),
        (globalPtrBits fl.N, fl.w)), 16 * b + lane), val)) :=
    ConfinedTo.writePackedComp_prog (htr.valid.w_eq ▸ htr.valid.w_pos)
      (nMax := 16 * numBucketsWhp fl.N) (by omega)
      fun addr ha1 ha2 => hbmM addr (by
        rw [BpMetaLayout.ofCtx_toCtx]
        exact Or.inr (Or.inr (Or.inl ⟨ha1, ha2⟩)))
  exact RWConfined.of_confined hcf (fun _ h => h) writeMeta_sub_readMeta

private theorem rw_fastReadBktCnt {w : ℕ} {fl : FastEpochLayout} {b : ℕ}
    {s : Memory.State} (htr : FastTableReady w fl s) :
    RWConfined (FastReadMeta fl) (FastWriteMeta fl) s (fastReadBktCntProg (fl.pBase, b)) := by
  unfold fastReadBktCntProg
  refine RWConfined.bind_readOnly_eq (rw_loadBpMetaCtx htr)
    (clientState_loadBpMetaCtxProg _ s) (clientResult_loadBpMetaCtxProg htr.pt) ?_
  exact RWConfined.of_confined (confinedTo_bpReadBktCountProg (bpMetaConf_fast htr.valid))
    (fun _ h => h) writeMeta_sub_readMeta

private theorem rw_fastBufLookup {w : ℕ} {fl : FastEpochLayout} {role rk : ℕ}
    {s : Memory.State} (htr : FastTableReady w fl s) :
    RWConfined (FastReadMeta fl) (FastWriteMeta fl) s
      (fastBufLookupProg ((fl.pBase, role), rk)) := by
  unfold fastBufLookupProg
  refine RWConfined.ite_prog (fun hrole => ?_) (fun _ => RWConfined.pure_prog _)
  refine RWConfined.bind_readOnly_eq rw_loadTrieCtx
    (clientState_loadTrieCtxProg _ s) (clientResult_loadTrieCtxProg htr.pt hrole) ?_
  exact RWConfined.of_confined (confinedTo_bufLookupBoundedProg (trieConf_fast htr.valid hrole))
    (fun _ h => h) writeMeta_sub_readMeta

private theorem rw_fastBufInsert {w : ℕ} {fl : FastEpochLayout} {role : ℕ}
    {rbl : ℕ × (ℕ × ℕ)} {s : Memory.State} (htr : FastTableReady w fl s) :
    RWConfined (FastReadMeta fl) (FastWriteMeta fl) s
      (fastBufInsertProg ((fl.pBase, role), rbl)) := by
  rcases rbl with ⟨rk, ⟨b, loc⟩⟩
  unfold fastBufInsertProg
  refine RWConfined.ite_prog (fun hrole => ?_) (fun _ => RWConfined.pure_prog _)
  refine RWConfined.bind_readOnly_eq rw_loadTrieCtx
    (clientState_loadTrieCtxProg _ s) (clientResult_loadTrieCtxProg htr.pt hrole) ?_
  exact RWConfined.of_confined (confinedTo_bufInsertBoundedProg (trieConf_fast htr.valid hrole))
    (fun _ h => h) writeMeta_sub_readMeta

private theorem rw_fastBufDelete {w : ℕ} {fl : FastEpochLayout} {role rk : ℕ}
    {s : Memory.State} (htr : FastTableReady w fl s) :
    RWConfined (FastReadMeta fl) (FastWriteMeta fl) s
      (fastBufDeleteProg ((fl.pBase, role), rk)) := by
  unfold fastBufDeleteProg
  refine RWConfined.ite_prog (fun hrole => ?_) (fun _ => RWConfined.pure_prog _)
  refine RWConfined.bind_readOnly_eq rw_loadTrieCtx
    (clientState_loadTrieCtxProg _ s) (clientResult_loadTrieCtxProg htr.pt hrole) ?_
  exact RWConfined.of_confined (confinedTo_bufDeleteBoundedProg (trieConf_fast htr.valid hrole))
    (fun _ h => h) writeMeta_sub_readMeta

private theorem rw_fastBufCheckSlot {w : ℕ} {fl : FastEpochLayout} {role id_v : ℕ}
    {s : Memory.State} (htr : FastTableReady w fl s) :
    RWConfined (FastReadMeta fl) (FastWriteMeta fl) s
      (fastBufCheckSlotProg ((fl.pBase, role), id_v)) := by
  unfold fastBufCheckSlotProg
  refine RWConfined.ite_prog (fun hrole => ?_) (fun _ => RWConfined.pure_prog _)
  refine RWConfined.bind_readOnly_eq rw_loadTrieCtx
    (clientState_loadTrieCtxProg _ s) (clientResult_loadTrieCtxProg htr.pt hrole) ?_
  exact RWConfined.of_confined (confinedTo_bufCheckSlotBoundedProg (trieConf_fast htr.valid hrole))
    (fun _ h => h) writeMeta_sub_readMeta

private theorem rw_fastBufClearSteps {w : ℕ} {fl : FastEpochLayout} {role : ℕ}
    {s : Memory.State} (htr : FastTableReady w fl s) :
    RWConfined (FastReadMeta fl) (FastWriteMeta fl) s
      (fastBufClearStepsProg (fl.pBase, role)) := by
  unfold fastBufClearStepsProg
  refine RWConfined.ite_prog (fun hrole => ?_) (fun _ => RWConfined.pure_prog _)
  refine RWConfined.bind_readOnly (rw_readParam (pBase_in_readMeta (by decide))) rfl ?_
  refine RWConfined.bind_readOnly_eq rw_loadTrieCtx
    (clientState_loadTrieCtxProg _ s) (clientResult_loadTrieCtxProg htr.pt hrole) ?_
  exact RWConfined.of_confined
    (confinedTo_bufClearStepsBoundedProg (trieConf_fast htr.valid hrole))
    (fun _ h => h) writeMeta_sub_readMeta

private theorem rw_fastBufItemAlloc {w : ℕ} {fl : FastEpochLayout} {role : ℕ}
    {s : Memory.State} (htr : FastTableReady w fl s) :
    RWConfined (FastReadMeta fl) (FastWriteMeta fl) s
      (fastBufItemAllocProg (fl.pBase, role)) := by
  unfold fastBufItemAllocProg
  refine RWConfined.ite_prog (fun hrole => ?_) (fun _ => RWConfined.pure_prog _)
  refine RWConfined.bind_readOnly_eq rw_loadTrieCtx
    (clientState_loadTrieCtxProg _ s) (clientResult_loadTrieCtxProg htr.pt hrole) ?_
  obtain ⟨_, _, htcM⟩ := trieConf_fast htr.valid hrole
  dsimp only [FastEpochLayout.trieL, epochTrieLayout, TrieLayout.toCtx]
  unfold readTrieItemAllocCtxProg
  refine RWConfined.ite_prog (fun _ => ?_) (fun _ => RWConfined.pure_prog _)
  have hcf : ConfinedTo (FastWriteMeta fl)
      (readPackedCompGenProg
        (((fl.metaBase, offTrieItem fl.c fl.w fl.N role), (globalPtrBits fl.N, fl.w)),
          6 * qEpochWhp fl.N + 1)) :=
    ConfinedTo.readPackedComp_prog (htr.valid.w_eq ▸ htr.valid.w_pos)
      (nMax := 6 * qEpochWhp fl.N + 6) (by omega)
      fun addr h1 h2 => htcM addr (by
        rw [TrieLayout.ofCtx_toCtx]
        exact Or.inr (Or.inr ⟨h1, h2⟩))
  exact RWConfined.of_confined hcf (fun _ h => h) writeMeta_sub_readMeta

private theorem rw_readParam2 {fl : FastEpochLayout} {i j : ℕ} (hi : i < 64) (hj : j < 64)
    (s : Memory.State) :
    RWConfined (FastReadMeta fl) (FastWriteMeta fl) s (readParam2Prog (fl.pBase, (i, j))) :=
  RWConfined.of_readOnly (fun _ => rfl) ((cf_readParamPair hi hj).res_eq s)

private theorem rw_readParam4 {fl : FastEpochLayout} {i j k l : ℕ}
    (hi : i < 64) (hj : j < 64) (hk : k < 64) (hl : l < 64) (s : Memory.State) :
    RWConfined (FastReadMeta fl) (FastWriteMeta fl) s
      (readParam4Prog ((fl.pBase, (i, j)), (k, l))) :=
  RWConfined.of_readOnly (fun _ => rfl) ((cf_readParamQuad hi hj hk hl).res_eq s)

private theorem rw_fastBTreeReset {w : ℕ} {fl : FastEpochLayout} {b role : ℕ}
    {s : Memory.State} (htr : FastTableReady w fl s) :
    RWConfined (FastReadMeta fl) (FastWriteMeta fl) s
      (fastBTreeResetProg (fl.pBase, (b, role))) := by
  unfold fastBTreeResetProg
  have h11 : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 11)) =
      numBucketsWhp fl.N := htr.pt 11 (by decide)
  refine RWConfined.bind_readOnly_eq (rw_readParam (pBase_in_readMeta (by decide))) rfl h11 ?_
  refine RWConfined.ite_prog (fun ⟨hb, hrole⟩ => ?_) (fun _ => RWConfined.pure_prog _)
  have hr1 : (Memory.spec 0).clientResult s (readParam2Prog (fl.pBase, (1, 31))) =
      (fl.metaBase, offBktMeta fl.c fl.w fl.N) := by
    unfold readParam2Prog
    simp [StateTransitionSpec.clientResult, htr.pt 1 (by decide), htr.pt 31 (by decide),
      FastEpochLayout.paramWord]
  have hr2 : (Memory.spec 0).clientResult s (readParam2Prog (fl.pBase, (10, 2))) =
      (globalPtrBits fl.N, fl.w) := by
    unfold readParam2Prog
    simp [StateTransitionSpec.clientResult, htr.pt 10 (by decide), htr.pt 2 (by decide),
      FastEpochLayout.paramWord]
  refine RWConfined.bind_readOnly_eq (rw_readParam2 (by decide) (by decide) s) rfl hr1 ?_
  refine RWConfined.bind_readOnly_eq (rw_readParam2 (by decide) (by decide) s) rfl hr2 ?_
  obtain ⟨_, _, hbmM⟩ := bpMetaConf_fast htr.valid
  have hw_pos : 0 < fl.w := htr.valid.w_eq ▸ htr.valid.w_pos
  have hw1 : ConfinedTo (FastWriteMeta fl)
      (writePackedCompGenProg ((((fl.metaBase, offBktMeta fl.c fl.w fl.N),
        (globalPtrBits fl.N, fl.w)), 16 * b + 6 + 2 * role), 0)) :=
    ConfinedTo.writePackedComp_prog hw_pos (nMax := 16 * numBucketsWhp fl.N) (by omega)
      fun addr h1 h2 => hbmM addr (by
        rw [BpMetaLayout.ofCtx_toCtx]
        exact Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))
  have hw2 : ConfinedTo (FastWriteMeta fl)
      (writePackedCompGenProg ((((fl.metaBase, offBktMeta fl.c fl.w fl.N),
        (globalPtrBits fl.N, fl.w)), 16 * b + 7 + 2 * role), 0)) :=
    ConfinedTo.writePackedComp_prog hw_pos (nMax := 16 * numBucketsWhp fl.N) (by omega)
      fun addr h1 h2 => hbmM addr (by
        rw [BpMetaLayout.ofCtx_toCtx]
        exact Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))
  exact RWConfined.of_confined (ConfinedTo.bind_prog hw1 fun _ => hw2) (fun _ h => h)
    writeMeta_sub_readMeta

private theorem rw_fastBTreeLookup {w : ℕ} {fl : FastEpochLayout} {b role q : ℕ}
    {s : Memory.State} (htr : FastTableReady w fl s) :
    RWConfined (FastReadMeta fl) (FastWriteMeta fl) s
      (fastBTreeLookupProg ((fl.pBase, (b, role)), q)) := by
  unfold fastBTreeLookupProg
  have h11 : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 11)) =
      numBucketsWhp fl.N := htr.pt 11 (by decide)
  refine RWConfined.bind_readOnly_eq (rw_readParam (pBase_in_readMeta (by decide))) rfl h11 ?_
  refine RWConfined.bind_readOnly (rw_readParam2 (by decide) (by decide) s) rfl ?_
  refine RWConfined.ite_prog (fun ⟨hb, hrole, _⟩ => RWConfined.ite_prog (fun _ => ?_)
    (fun _ => RWConfined.pure_prog _)) (fun _ => RWConfined.pure_prog _)
  refine RWConfined.bind_readOnly_eq rw_loadBTreeSliceCtx
    (clientState_loadBTreeSliceCtxProg _ s) (clientResult_loadBTreeSliceCtxProg htr.pt) ?_
  exact RWConfined.of_confined
    (confinedTo_btreeLookupBoundedProg (btreeSliceConf_fast htr.valid hb hrole))
    (fun _ h => h) writeMeta_sub_readMeta

private theorem rw_fastBTreeDelete {w : ℕ} {fl : FastEpochLayout} {b role q : ℕ}
    {s : Memory.State} (htr : FastTableReady w fl s) :
    RWConfined (FastReadMeta fl) (FastWriteMeta fl) s
      (fastBTreeDeleteProg ((fl.pBase, (b, role)), q)) := by
  unfold fastBTreeDeleteProg
  have h11 : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 11)) =
      numBucketsWhp fl.N := htr.pt 11 (by decide)
  refine RWConfined.bind_readOnly_eq (rw_readParam (pBase_in_readMeta (by decide))) rfl h11 ?_
  refine RWConfined.bind_readOnly (rw_readParam2 (by decide) (by decide) s) rfl ?_
  refine RWConfined.ite_prog (fun ⟨hb, hrole, _⟩ => RWConfined.ite_prog (fun _ => ?_)
    (fun _ => RWConfined.pure_prog _)) (fun _ => RWConfined.pure_prog _)
  refine RWConfined.bind_readOnly_eq rw_loadBTreeSliceCtx
    (clientState_loadBTreeSliceCtxProg _ s) (clientResult_loadBTreeSliceCtxProg htr.pt) ?_
  exact RWConfined.of_confined
    (confinedTo_btreeDeleteBoundedProg (btreeSliceConf_fast htr.valid hb hrole))
    (fun _ h => h) writeMeta_sub_readMeta

private theorem rw_fastBTreeUpdate {w : ℕ} {fl : FastEpochLayout} {b role q newVal : ℕ}
    {s : Memory.State} (htr : FastTableReady w fl s) :
    RWConfined (FastReadMeta fl) (FastWriteMeta fl) s
      (fastBTreeUpdateProg ((fl.pBase, (b, role)), (q, newVal))) := by
  unfold fastBTreeUpdateProg
  have h11 : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 11)) =
      numBucketsWhp fl.N := htr.pt 11 (by decide)
  refine RWConfined.bind_readOnly_eq (rw_readParam (pBase_in_readMeta (by decide))) rfl h11 ?_
  refine RWConfined.bind_readOnly (rw_readParam4 (by decide) (by decide) (by decide) (by decide) s)
    rfl ?_
  refine RWConfined.ite_prog (fun ⟨hb, hrole, _⟩ => RWConfined.ite_prog (fun _ => ?_)
    (fun _ => RWConfined.pure_prog _)) (fun _ => RWConfined.pure_prog _)
  refine RWConfined.bind_readOnly_eq rw_loadBTreeSliceCtx
    (clientState_loadBTreeSliceCtxProg _ s) (clientResult_loadBTreeSliceCtxProg htr.pt) ?_
  exact RWConfined.of_confined
    (confinedTo_btreeUpdateBoundedProg (btreeSliceConf_fast htr.valid hb hrole))
    (fun _ h => h) writeMeta_sub_readMeta

private theorem rw_fastBTreeInsert {w : ℕ} {fl : FastEpochLayout} {b role q val : ℕ}
    {s : Memory.State} (htr : FastTableReady w fl s) :
    RWConfined (FastReadMeta fl) (FastWriteMeta fl) s
      (fastBTreeInsertProg ((fl.pBase, (b, role)), (q, val))) := by
  unfold fastBTreeInsertProg
  have h11 : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 11)) =
      numBucketsWhp fl.N := htr.pt 11 (by decide)
  refine RWConfined.bind_readOnly_eq (rw_readParam (pBase_in_readMeta (by decide))) rfl h11 ?_
  refine RWConfined.bind_readOnly (rw_readParam4 (by decide) (by decide) (by decide) (by decide) s)
    rfl ?_
  refine RWConfined.ite_prog (fun ⟨hb, hrole, _⟩ => RWConfined.ite_prog (fun _ => ?_)
    (fun _ => RWConfined.pure_prog _)) (fun _ => RWConfined.pure_prog _)
  refine RWConfined.bind_readOnly_eq rw_loadBTreeSliceCtx
    (clientState_loadBTreeSliceCtxProg _ s) (clientResult_loadBTreeSliceCtxProg htr.pt) ?_
  exact RWConfined.of_confined
    (confinedTo_btreeInsertBoundedProg (btreeSliceConf_fast htr.valid hb hrole))
    (fun _ h => h) writeMeta_sub_readMeta

private theorem rw_shadowRole (fl : FastEpochLayout) (r : ℕ) (s : Memory.State) :
    RWConfined (FastReadMeta fl) (FastWriteMeta fl) s (shadowRoleProg r) := by
  unfold shadowRoleProg
  exact RWConfined.ite_prog (fun _ => RWConfined.pure_prog _) fun _ =>
    RWConfined.ite_prog (fun _ => RWConfined.pure_prog _) (fun _ => RWConfined.pure_prog _)

private theorem rw_tryRole (fl : FastEpochLayout) (r : ℕ) (s : Memory.State) :
    RWConfined (FastReadMeta fl) (FastWriteMeta fl) s (tryRoleProg r) := by
  unfold tryRoleProg
  exact RWConfined.ite_prog (fun _ => RWConfined.pure_prog _) fun _ =>
    RWConfined.ite_prog (fun _ => RWConfined.pure_prog _) (fun _ => RWConfined.pure_prog _)

/-! ## Section 3: Metadata-Only Helpers & Direct-Mode (`usePaged = 0`) Epoch Operations -/

private theorem rw_writeTryResetMeta {w : ℕ} {fl : FastEpochLayout} {ns : ℕ}
    {s : Memory.State} (htr : FastTableReady w fl s) :
    RWConfined (FastReadMeta fl) (FastWriteMeta fl) s
      (writeTryResetMetaProg (fl.pBase, ns)) := by
  unfold writeTryResetMetaProg
  refine rw_bind_meta htr (rw_fastWriteMeta htr) fun s1 h1 _ => ?_
  refine rw_bind_meta h1 (rw_fastWriteMeta h1) fun _ h2 _ => ?_
  exact rw_fastWriteMeta h2

private theorem rw_nextSalt (fl : FastEpochLayout) (ab : ℕ × ℕ) (s : Memory.State) :
    RWConfined (FastReadMeta fl) (FastWriteMeta fl) s (nextSaltProg ab) := by
  rcases ab with ⟨_, _⟩
  unfold nextSaltProg
  exact RWConfined.ite_prog
    (fun _ => RWConfined.ite_prog (fun _ => RWConfined.pure_prog _)
      (fun _ => RWConfined.pure_prog _))
    (fun _ => RWConfined.pure_prog _)

private theorem rw_advanceTrySalt {w : ℕ} {fl : FastEpochLayout}
    {s : Memory.State} (htr : FastTableReady w fl s) :
    RWConfined (FastReadMeta fl) (FastWriteMeta fl) s (advanceTrySaltProg fl.pBase) := by
  unfold advanceTrySaltProg
  refine rw_bind_meta htr (rw_fastReadMeta htr) fun _ h1 _ => ?_
  refine rw_bind_meta h1 (rw_fastReadMeta h1) fun _ h2 _ => ?_
  refine rw_bind_meta h2 (rw_readParam (pBase_in_readMeta (by decide))) fun s3 h3 _ => ?_
  refine rw_bind_meta h3 (rw_nextSalt fl _ s3) fun _ h4 _ => ?_
  refine rw_bind_meta h4 (rw_fastReadBktLane h4) fun s5 h5 _ => ?_
  refine rw_bind_meta h5 (rw_tryRole fl _ s5) fun _ h6 _ => ?_
  refine rw_bind_meta h6 (rw_fastBTreeReset h6) fun _ h7 _ => ?_
  exact rw_writeTryResetMeta h7

private theorem rw_commitTrySalt {w : ℕ} {fl : FastEpochLayout}
    {s : Memory.State} (htr : FastTableReady w fl s) :
    RWConfined (FastReadMeta fl) (FastWriteMeta fl) s (commitTrySaltProg fl.pBase) := by
  unfold commitTrySaltProg clearTryMetaProg
  refine rw_bind_meta htr (rw_fastReadMeta htr) fun _ h1 _ => ?_
  refine rw_bind_meta h1 (rw_fastReadMeta h1) fun _ h2 _ => ?_
  refine rw_bind_meta h2 (rw_fastReadMeta h2) fun _ h3 _ => ?_
  refine rw_bind_meta h3 (rw_fastReadBktLane h3) fun s4 h4 _ => ?_
  refine rw_bind_meta h4 (rw_tryRole fl _ s4) fun _ h5 _ => ?_
  refine rw_bind_meta h5 (rw_fastWriteBktLane h5) fun _ h6 _ => ?_
  refine rw_bind_meta h6 (rw_fastWriteBktLane h6) fun _ h7 _ => ?_
  refine rw_bind_meta h7 (rw_fastWriteBktLane h7) fun _ h8 _ => ?_
  refine rw_bind_meta h8 (rw_fastWriteMeta h8) fun _ h9 _ => ?_
  refine rw_bind_meta h9 (rw_fastWriteMeta h9) fun _ h10 _ => ?_
  exact rw_fastWriteMeta h10

private theorem rw_startTrySalt {w : ℕ} {fl : FastEpochLayout} {b : ℕ}
    {s : Memory.State} (htr : FastTableReady w fl s) :
    RWConfined (FastReadMeta fl) (FastWriteMeta fl) s (startTrySaltProg (fl.pBase, b)) := by
  unfold startTrySaltProg writeStartTryMetaProg
  refine rw_bind_meta htr (rw_fastReadBktLane htr) fun s1 h1 _ => ?_
  refine rw_bind_meta h1 (rw_tryRole fl _ s1) fun _ h2 _ => ?_
  refine rw_bind_meta h2 (rw_fastBTreeReset h2) fun _ h3 _ => ?_
  refine rw_bind_meta h3 (rw_fastWriteMeta h3) fun _ h4 _ => ?_
  refine rw_bind_meta h4 (rw_fastWriteMeta h4) fun _ h5 _ => ?_
  exact rw_writeTryResetMeta h5

private theorem rw_fastDelShadowTryStep {w : ℕ} {fl : FastEpochLayout} {b role fp delLoc : ℕ}
    {s : Memory.State} (htr : FastTableReady w fl s) :
    RWConfined (FastReadMeta fl) (FastWriteMeta fl) s
      (fastDelShadowTryStepProg ((fl.pBase, (b, role)), (fp, delLoc))) := by
  unfold fastDelShadowTryStepProg
  refine rw_bind_meta htr (rw_fastReadBktLane htr) fun s1 h1 _ => ?_
  refine RWConfined.ite_prog (fun _ => ?_) (fun _ => RWConfined.pure_prog _)
  refine rw_bind_meta h1 (rw_shadowRole fl role s1) fun _ h2 _ => ?_
  exact rw_fastBTreeDelete h2

private theorem rw_fastDelTryStep {w : ℕ} {fl : FastEpochLayout} {b role delLoc u_val : ℕ}
    {s : Memory.State} (htr : FastTableReady w fl s) :
    RWConfined (FastReadMeta fl) (FastWriteMeta fl) s
      (fastDelTryStepProg ((fl.pBase, (b, role)), (delLoc, u_val))) := by
  unfold fastDelTryStepProg
  refine rw_bind_meta htr (rw_fastReadMeta htr) fun _ h1 _ => ?_
  refine rw_bind_meta h1 (rw_fastReadMeta h1) fun _ h2 _ => ?_
  refine rw_bind_meta h2 (rw_fastReadMeta h2) fun _ h3 _ => ?_
  refine RWConfined.ite_prog (fun _ => ?_) (fun _ => RWConfined.pure_prog _)
  refine rw_bind_meta h3 (rw_fastReadMeta h3) fun _ h4 _ => ?_
  refine rw_bind_meta h4 (rw_fastFpHash h4) fun s5 h5 _ => ?_
  refine rw_bind_meta h5 (rw_tryRole fl role s5) fun _ h6 _ => ?_
  exact rw_fastBTreeDelete h6

private theorem rw_fastDeleteFromBTrees {w : ℕ} {fl : FastEpochLayout} {b delLoc u_val : ℕ}
    {s : Memory.State} (htr : FastTableReady w fl s) :
    RWConfined (FastReadMeta fl) (FastWriteMeta fl) s
      (fastDeleteFromBTreesProg ((fl.pBase, (b, delLoc)), u_val)) := by
  unfold fastDeleteFromBTreesProg
  refine rw_bind_meta htr (rw_readParam (pBase_in_readMeta (by decide))) fun _ h1 _ => ?_
  refine RWConfined.ite_prog (fun _ => ?_) (fun _ => RWConfined.pure_prog _)
  refine rw_bind_meta h1 (rw_fastReadBktLane h1) fun _ h2 _ => ?_
  refine rw_bind_meta h2 (rw_fastReadBktLane h2) fun _ h3 _ => ?_
  refine rw_bind_meta h3 (rw_fastFpHash h3) fun _ h4 _ => ?_
  refine rw_bind_meta h4 (rw_fastBTreeDelete h4) fun _ h5 _ => ?_
  refine rw_bind_meta h5 (rw_fastDelShadowTryStep h5) fun _ h6 _ => ?_
  exact rw_fastDelTryStep h6

private theorem rw_fastUnindexAt {w : ℕ} {fl : FastEpochLayout} {b delLoc u_val : ℕ}
    {s : Memory.State} (htr : FastTableReady w fl s) :
    RWConfined (FastReadMeta fl) (FastWriteMeta fl) s
      (fastUnindexAtProg ((fl.pBase, (b, delLoc)), u_val)) := by
  unfold fastUnindexAtProg
  refine rw_bind_meta htr (rw_fastRKey htr) fun _ h1 _ => ?_
  refine rw_bind_meta h1 (rw_fastReadMeta h1) fun _ h2 _ => ?_
  refine RWConfined.ite_prog (fun _ => ?_) (fun _ => RWConfined.pure_prog _)
  refine rw_bind_meta h2 (rw_fastBufLookup h2) fun _ h3 _ => ?_
  refine RWConfined.ite_prog (fun _ => rw_fastBufDelete h3) fun _ => ?_
  refine rw_bind_meta h3 (rw_fastReadMeta h3) fun _ h4 _ => ?_
  refine rw_bind_meta h4 (rw_readParam (pBase_in_readMeta (by decide))) fun _ h5 _ => ?_
  refine RWConfined.ite_prog (fun _ => ?_) (fun _ => rw_fastDeleteFromBTrees h5)
  simp only [pure_bind]
  refine rw_bind_meta h5 (rw_fastBufLookup h5) fun _ h6 _ => ?_
  exact RWConfined.ite_prog (fun _ => rw_fastBufDelete h6)
    (fun _ => rw_fastDeleteFromBTrees h6)

private theorem rw_fastRelocShadowStep {w : ℕ} {fl : FastEpochLayout} {b role fp delLoc : ℕ}
    {s : Memory.State} (htr : FastTableReady w fl s) :
    RWConfined (FastReadMeta fl) (FastWriteMeta fl) s
      (fastRelocShadowStepProg ((fl.pBase, (b, role)), (fp, delLoc))) := by
  unfold fastRelocShadowStepProg
  refine rw_bind_meta htr (rw_fastReadBktLane htr) fun _ h1 _ => ?_
  refine rw_bind_meta h1 (rw_readParam (pBase_in_readMeta (by decide))) fun s2 h2 _ => ?_
  refine RWConfined.ite_prog (fun _ => ?_) (fun _ => RWConfined.pure_prog _)
  refine rw_bind_meta h2 (rw_shadowRole fl role s2) fun _ h3 _ => ?_
  refine rw_bind_meta h3 (rw_fastBTreeInsert h3) fun _ h4 _ => ?_
  refine rw_bind_meta h4 (rw_fastReadBktLane h4) fun _ h5 _ => ?_
  exact RWConfined.ite_prog (fun _ => rw_fastWriteBktLane h5) (fun _ => RWConfined.pure_prog _)

private theorem rw_fastRelocTryStep {w : ℕ} {fl : FastEpochLayout}
    {b role delLoc lastLoc u_last : ℕ} {s : Memory.State} (htr : FastTableReady w fl s) :
    RWConfined (FastReadMeta fl) (FastWriteMeta fl) s
      (fastRelocTryStepProg ((fl.pBase, (b, role)), ((delLoc, lastLoc), u_last))) := by
  unfold fastRelocTryStepProg
  refine rw_bind_meta htr (rw_fastReadMeta htr) fun _ h1 _ => ?_
  refine rw_bind_meta h1 (rw_fastReadMeta h1) fun _ h2 _ => ?_
  refine rw_bind_meta h2 (rw_fastReadMeta h2) fun _ h3 _ => ?_
  refine RWConfined.ite_prog (fun _ => ?_) (fun _ => RWConfined.pure_prog _)
  refine rw_bind_meta h3 (rw_fastReadMeta h3) fun _ h4 _ => ?_
  refine rw_bind_meta h4 (rw_fastFpHash h4) fun s5 h5 _ => ?_
  refine rw_bind_meta h5 (rw_tryRole fl role s5) fun _ h6 _ => ?_
  refine RWConfined.ite_prog (fun _ => rw_fastBTreeUpdate h6) fun _ => ?_
  refine RWConfined.ite_prog (fun _ => ?_) (fun _ => RWConfined.pure_prog _)
  unfold fastRelocTryInsProg
  refine rw_bind_meta h6 (rw_fastBTreeLookup h6) fun _ h7 _ => ?_
  refine RWConfined.ite_prog (fun _ => rw_advanceTrySalt h7) fun _ => ?_
  refine rw_bind_meta h7 (rw_readParam (pBase_in_readMeta (by decide))) fun _ h8 _ => ?_
  refine rw_bind_meta h8 (rw_fastBTreeInsert h8) fun _ h9 _ => ?_
  refine rw_bind_meta h9 (rw_fastReadMeta h9) fun _ h10 _ => ?_
  exact RWConfined.ite_prog (fun _ => rw_fastWriteMeta h10) (fun _ => RWConfined.pure_prog _)

private theorem rw_fastRelocBTree {w : ℕ} {fl : FastEpochLayout}
    {b delLoc lastLoc u_last : ℕ} {s : Memory.State} (htr : FastTableReady w fl s) :
    RWConfined (FastReadMeta fl) (FastWriteMeta fl) s
      (fastRelocBTreeProg ((fl.pBase, (b, delLoc)), (lastLoc, u_last))) := by
  unfold fastRelocBTreeProg
  refine rw_bind_meta htr (rw_readParam (pBase_in_readMeta (by decide))) fun _ h1 _ => ?_
  refine RWConfined.ite_prog (fun _ => ?_) (fun _ => RWConfined.pure_prog _)
  refine rw_bind_meta h1 (rw_fastReadBktLane h1) fun _ h2 _ => ?_
  refine rw_bind_meta h2 (rw_fastReadBktLane h2) fun _ h3 _ => ?_
  refine rw_bind_meta h3 (rw_fastFpHash h3) fun _ h4 _ => ?_
  refine rw_bind_meta h4 (rw_fastBTreeUpdate h4) fun _ h5 _ => ?_
  refine rw_bind_meta h5 (rw_fastRelocShadowStep h5) fun _ h6 _ => ?_
  exact rw_fastRelocTryStep h6

private theorem rw_fastRelocLast {w : ℕ} {fl : FastEpochLayout}
    {b delLoc lastLoc u_last : ℕ} {s : Memory.State} (htr : FastTableReady w fl s) :
    RWConfined (FastReadMeta fl) (FastWriteMeta fl) s
      (fastRelocLastProg ((fl.pBase, (b, delLoc)), (lastLoc, u_last))) := by
  unfold fastRelocLastProg
  refine rw_bind_meta htr (rw_fastRKey htr) fun _ h1 _ => ?_
  refine rw_bind_meta h1 (rw_fastReadMeta h1) fun _ h2 _ => ?_
  refine RWConfined.ite_prog (fun _ => ?_) (fun _ => RWConfined.pure_prog _)
  refine rw_bind_meta h2 (rw_fastBufLookup h2) fun _ h3 _ => ?_
  refine RWConfined.ite_prog (fun _ => rw_fastBufInsert h3) fun _ => ?_
  refine rw_bind_meta h3 (rw_fastReadMeta h3) fun _ h4 _ => ?_
  refine rw_bind_meta h4 (rw_readParam (pBase_in_readMeta (by decide))) fun _ h5 _ => ?_
  refine RWConfined.ite_prog (fun _ => ?_) (fun _ => rw_fastRelocBTree h5)
  simp only [pure_bind]
  refine rw_bind_meta h5 (rw_fastBufLookup h5) fun _ h6 _ => ?_
  exact RWConfined.ite_prog (fun _ => rw_fastBufInsert h6) (fun _ => rw_fastRelocBTree h6)

private theorem rw_fastPromoteShadowIfDone {w : ℕ} {fl : FastEpochLayout} {b cnt : ℕ}
    {s : Memory.State} (htr : FastTableReady w fl s) :
    RWConfined (FastReadMeta fl) (FastWriteMeta fl) s
      (fastPromoteShadowIfDoneProg ((fl.pBase, b), cnt)) := by
  unfold fastPromoteShadowIfDoneProg
  refine rw_bind_meta htr (rw_fastReadBktLane htr) fun _ h1 _ => ?_
  refine RWConfined.ite_prog (fun _ => ?_) (fun _ => RWConfined.pure_prog _)
  refine rw_bind_meta h1 (rw_fastReadBktLane h1) fun s2 h2 _ => ?_
  refine rw_bind_meta h2 (rw_shadowRole fl _ s2) fun _ h3 _ => ?_
  refine rw_bind_meta h3 (rw_fastReadBktLane h3) fun _ h4 _ => ?_
  refine rw_bind_meta h4 (rw_fastWriteBktLane h4) fun _ h5 _ => ?_
  refine rw_bind_meta h5 (rw_fastWriteBktLane h5) fun _ h6 _ => ?_
  exact rw_fastWriteBktLane h6

private theorem rw_fastClampTryPos {w : ℕ} {fl : FastEpochLayout} {b cnt lastLoc : ℕ}
    {s : Memory.State} (htr : FastTableReady w fl s) :
    RWConfined (FastReadMeta fl) (FastWriteMeta fl) s
      (fastClampTryPosProg ((fl.pBase, b), (cnt, lastLoc))) := by
  unfold fastClampTryPosProg
  refine rw_bind_meta htr (rw_fastReadMeta htr) fun _ h1 _ => ?_
  refine rw_bind_meta h1 (rw_fastReadMeta h1) fun _ h2 _ => ?_
  refine rw_bind_meta h2 (rw_fastReadMeta h2) fun _ h3 _ => ?_
  exact RWConfined.ite_prog (fun _ => rw_fastWriteMeta h3) (fun _ => RWConfined.pure_prog _)

/-! ### Direct-Mode (`io.usePaged = 0`) Epoch Mutations -/

private theorem slotIoDirectConf_fast {w : ℕ} {fl : FastEpochLayout} {fr : ℕ}
    (hv : fl.Valid w fr) (hup : fl.io.usePaged = 0) :
    SlotIoDirectConf fl.OwnsFastAddr fl.io.toCtx := by
  dsimp only [SlotIoDirectConf]
  rw [SlotIoLayout.ofCtx_toCtx]
  exact ⟨hup, hv.w_eq_io ▸ hv.w_eq ▸ hv.w_pos, fun addr ha => Or.inr (Or.inr ha)⟩

private theorem bpMetaConf_fastDirect {w : ℕ} {fl : FastEpochLayout} {fr : ℕ}
    (hv : fl.Valid w fr) : BpMetaConf fl.OwnsFastAddr fl.mp.toCtx := by
  obtain ⟨h1, h2, h3⟩ := bpMetaConf_fast hv
  exact ⟨h1, h2, fun addr ha => writeMeta_sub_ownsFast addr (h3 addr ha)⟩

private theorem bpMetaConf_readDirect {w : ℕ} {fl : FastEpochLayout} {fr : ℕ}
    (hv : fl.Valid w fr) : BpMetaConf (FastReadDirect fl) fl.mp.toCtx := by
  obtain ⟨h1, h2, h3⟩ := bpMetaConf_fastDirect hv
  exact ⟨h1, h2, fun addr ha => ownsFast_sub_readDirect addr (h3 addr ha)⟩

private theorem slotIoDirectConf_readDirect {w : ℕ} {fl : FastEpochLayout} {fr : ℕ}
    (hv : fl.Valid w fr) (hup : fl.io.usePaged = 0) :
    SlotIoDirectConf (FastReadDirect fl) fl.io.toCtx := by
  obtain ⟨h1, h2, h3⟩ := slotIoDirectConf_fast hv hup
  exact ⟨h1, h2, fun addr ha => ownsFast_sub_readDirect addr (h3 addr ha)⟩

private theorem feistelConf_bktDirect {w : ℕ} {fl : FastEpochLayout} {fr : ℕ}
    (hv : fl.Valid w fr) : FeistelConf (FastReadDirect fl) fl.feistelCtx := by
  obtain ⟨h1, h2, h3⟩ := feistelConf_bkt hv
  exact ⟨h1, h2, fun addr ha1 ha2 => Or.inl (h3 addr ha1 ha2)⟩

private theorem rw_fastBpReadAt_direct {w : ℕ} {fl : FastEpochLayout} {b loc : ℕ}
    {s : Memory.State} (htr : FastTableReady w fl s) (hup : fl.io.usePaged = 0) :
    RWConfined (FastReadDirect fl) fl.OwnsFastAddr s (fastBpReadAtProg (fl.pBase, (b, loc))) := by
  unfold fastBpReadAtProg
  refine RWConfined.bind_readOnly_eq (rw_meta_to_direct (rw_loadBlockPoolCtx htr))
    (clientState_loadBlockPoolCtxProg _ s) (clientResult_loadBlockPoolCtxProg htr.pt) ?_
  dsimp only [BlockPoolLayout.toCtx, FastEpochLayout.bpL]
  have hcf := confinedTo_bpReadAtRawProg (b := b) (loc := loc)
    (bpMetaConf_fastDirect htr.valid) (slotIoDirectConf_fast htr.valid hup)
  unfold bpReadAtRawProg at hcf
  exact RWConfined.of_confined hcf (fun _ h => h) ownsFast_sub_readDirect

private theorem rw_fastBpWriteAt_direct {w : ℕ} {fl : FastEpochLayout} {b loc : ℕ} {qv : ℕ × ℕ}
    {s : Memory.State} (htr : FastTableReady w fl s) (hup : fl.io.usePaged = 0) :
    RWConfined (FastReadDirect fl) fl.OwnsFastAddr s
      (fastBpWriteAtProg ((fl.pBase, (b, loc)), qv)) := by
  unfold fastBpWriteAtProg
  refine RWConfined.bind_readOnly_eq (rw_meta_to_direct (rw_loadBlockPoolCtx htr))
    (clientState_loadBlockPoolCtxProg _ s) (clientResult_loadBlockPoolCtxProg htr.pt) ?_
  exact RWConfined.of_confined
    (confinedTo_bpWriteAtRawProg (bpMetaConf_fastDirect htr.valid)
      (slotIoDirectConf_fast htr.valid hup))
    (fun _ h => h) ownsFast_sub_readDirect

private theorem rw_fastBpAppend_direct {w : ℕ} {fl : FastEpochLayout} {b : ℕ} {qv : ℕ × ℕ}
    {s : Memory.State} (htr : FastTableReady w fl s) (hup : fl.io.usePaged = 0) :
    RWConfined (FastReadDirect fl) fl.OwnsFastAddr s
      (fastBpAppendProg ((fl.pBase, b), qv)) := by
  unfold fastBpAppendProg
  refine RWConfined.bind_readOnly_eq (rw_meta_to_direct (rw_loadBlockPoolCtx htr))
    (clientState_loadBlockPoolCtxProg _ s) (clientResult_loadBlockPoolCtxProg htr.pt) ?_
  exact RWConfined.of_confined
    (confinedTo_bpAppendRawProg (bpMetaConf_fastDirect htr.valid)
      (slotIoDirectConf_fast htr.valid hup))
    (fun _ h => h) ownsFast_sub_readDirect

private theorem rw_fastBpPopBktBack_direct {w : ℕ} {fl : FastEpochLayout} {b : ℕ}
    {s : Memory.State} (htr : FastTableReady w fl s) (hup : fl.io.usePaged = 0) :
    RWConfined (FastReadDirect fl) fl.OwnsFastAddr s
      (fastBpPopBktBackProg (fl.pBase, b)) := by
  unfold fastBpPopBktBackProg
  refine RWConfined.bind_readOnly_eq (rw_meta_to_direct (rw_loadBlockPoolCtx htr))
    (clientState_loadBlockPoolCtxProg _ s) (clientResult_loadBlockPoolCtxProg htr.pt) ?_
  exact RWConfined.of_confined
    (confinedTo_bpPopBktBackRawProg (bpMetaConf_fastDirect htr.valid)
      (slotIoDirectConf_fast htr.valid hup))
    (fun _ h => h) ownsFast_sub_readDirect

private theorem rw_fastEnterFallback_direct {w : ℕ} {fl : FastEpochLayout}
    {s : Memory.State} (htr : FastTableReady w fl s) (hup : fl.io.usePaged = 0) :
    RWConfined (FastReadDirect fl) fl.OwnsFastAddr s (fastEnterFallbackProg fl.pBase) := by
  unfold fastEnterFallbackProg
  refine RWConfined.bind_readOnly_eq (rw_meta_to_direct (rw_loadBlockPoolCtx htr))
    (clientState_loadBlockPoolCtxProg _ s) (clientResult_loadBlockPoolCtxProg htr.pt) ?_
  have hm2 : fl.OwnsFastAddr ((BpMetaLayout.ofCtx fl.mp.toCtx).metaBase + 2) := by
    rw [BpMetaLayout.ofCtx_toCtx]
    exact Or.inl ⟨by dsimp [FastEpochLayout.mp, epochBpMetaLayout]; omega,
      by dsimp [FastEpochLayout.mp, epochBpMetaLayout]; omega⟩
  exact RWConfined.of_confined
    (confinedTo_enterFallbackProg hm2 (bpMetaConf_fastDirect htr.valid)
      (slotIoDirectConf_fast htr.valid hup))
    (fun _ h => h) ownsFast_sub_readDirect

private theorem rw_fastFallbackBody_direct {α : Type} {w u_val : ℕ} {fl : FastEpochLayout}
    {s : Memory.State} (htr : FastTableReady w fl s) (dflt : α)
    (k : FeistelHashCtx → BlockPoolCtx → Memory.Prog α)
    (hk : ConfinedTo (FastReadDirect fl) (k fl.feistelCtx fl.bpL.toCtx)) :
    RWConfined (FastReadDirect fl) (FastReadDirect fl) s
      (do
        let uMax ← Memory.read (fl.pBase + 46)
        if u_val ≤ uMax then do
          let fctx ← loadHashStaticCtxProg (fl.pBase, 0)
          let bpCtx ← loadBlockPoolCtxProg fl.pBase
          k fctx bpCtx
        else pure dflt) := by
  have hp46 : RWConfined (FastReadDirect fl) (FastReadDirect fl) s
      (Memory.read (fl.pBase + 46)) :=
    RWConfined.read_prog (Or.inl (pBase_in_readMeta (by decide)))
  refine RWConfined.bind_readOnly hp46 rfl ?_
  refine RWConfined.ite_prog (fun _ => ?_) (fun _ => RWConfined.pure_prog _)
  have hl1 : RWConfined (FastReadDirect fl) (FastReadDirect fl) s
      (loadHashStaticCtxProg (fl.pBase, 0)) :=
    (rw_loadHashStaticCtx (W := FastWriteMeta fl)).mono writeMeta_sub_readMeta (fun _ => Or.inl)
      (fun a hw => Or.inl (writeMeta_sub_readMeta a hw))
  have hl2 : RWConfined (FastReadDirect fl) (FastReadDirect fl) s
      (loadBlockPoolCtxProg fl.pBase) :=
    (rw_loadBlockPoolCtx (W := FastWriteMeta fl) htr).mono writeMeta_sub_readMeta (fun _ => Or.inl)
      (fun a hw => Or.inl (writeMeta_sub_readMeta a hw))
  refine RWConfined.bind_readOnly_eq hl1 (clientState_loadHashStaticCtxProg _ s)
    (clientResult_loadFeistelCtx htr.pt) ?_
  refine RWConfined.bind_readOnly_eq hl2 (clientState_loadBlockPoolCtxProg _ s)
    (clientResult_loadBlockPoolCtxProg htr.pt) ?_
  exact RWConfined.of_confined hk (fun _ h => h) (fun _ h => h)

private theorem rw_fastFallbackInsert_direct {w : ℕ} {fl : FastEpochLayout} {u_val v_val : ℕ}
    {s : Memory.State} (htr : FastTableReady w fl s) (hup : fl.io.usePaged = 0) :
    RWConfined (FastReadDirect fl) (FastReadDirect fl) s
      (fastFallbackInsertProg ((fl.pBase, u_val), v_val)) := by
  unfold fastFallbackInsertProg
  exact rw_fastFallbackBody_direct htr ()
    (fun fctx bpCtx => fallbackInsertProg (((fctx, bpCtx), u_val), v_val))
    (confinedTo_fallbackInsertProg (feistelConf_bktDirect htr.valid)
      (bpMetaConf_readDirect htr.valid) (slotIoDirectConf_readDirect htr.valid hup))

private theorem rw_fastFallbackDelete_direct {w : ℕ} {fl : FastEpochLayout} {u_val : ℕ}
    {s : Memory.State} (htr : FastTableReady w fl s) (hup : fl.io.usePaged = 0) :
    RWConfined (FastReadDirect fl) (FastReadDirect fl) s
      (fastFallbackDeleteProg (fl.pBase, u_val)) := by
  unfold fastFallbackDeleteProg
  exact rw_fastFallbackBody_direct htr ()
    (fun fctx bpCtx => fallbackDeleteProg ((fctx, bpCtx), u_val))
    (confinedTo_fallbackDeleteProg (feistelConf_bktDirect htr.valid)
      (bpMetaConf_readDirect htr.valid) (slotIoDirectConf_readDirect htr.valid hup))

private theorem rw_fastCheckTrieRole_direct {w : ℕ} {fl : FastEpochLayout} {role rk : ℕ}
    {bq : ℕ × ℕ} {s : Memory.State} (htr : FastTableReady w fl s) (hup : fl.io.usePaged = 0)
    (hrole : role < 2) :
    RWConfined (FastReadDirect fl) fl.OwnsFastAddr s
      (fastCheckTrieRoleProg ((fl.pBase, role), (rk, bq))) := by
  rcases bq with ⟨b, q_u⟩
  unfold fastCheckTrieRoleProg
  refine RWConfined.bind_readOnly_eq (rw_meta_to_direct rw_loadTrieCtx)
    (clientState_loadTrieCtxProg _ s) (clientResult_loadTrieCtxProg htr.pt hrole) ?_
  refine rw_bind_direct htr
    (rw_meta_to_direct (RWConfined.of_confined
      (confinedTo_bufLookupBoundedProg (rKey := rk) (trieConf_fast htr.valid hrole))
      (fun _ h => h) writeMeta_sub_readMeta))
    fun _ h1 ⟨_, ⟨_, _⟩⟩ => ?_
  refine RWConfined.ite_prog (fun _ => ?_) (fun _ => RWConfined.pure_prog _)
  refine rw_bind_direct h1 (rw_fastBpReadAt_direct h1 hup) fun _ _ _ => ?_
  exact RWConfined.ite_prog
    (fun _ => RWConfined.ite_prog (fun _ => RWConfined.pure_prog _)
      (fun _ => RWConfined.pure_prog _))
    (fun _ => RWConfined.pure_prog _)

private theorem rw_fastCheckBTree_direct {w : ℕ} {fl : FastEpochLayout} {u_val b q_u : ℕ}
    {s : Memory.State} (htr : FastTableReady w fl s) (hup : fl.io.usePaged = 0) :
    RWConfined (FastReadDirect fl) fl.OwnsFastAddr s
      (fastCheckBTreeProg ((fl.pBase, u_val), (b, q_u))) := by
  unfold fastCheckBTreeProg
  have h11 : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 11)) =
      numBucketsWhp fl.N := htr.pt 11 (by decide)
  refine RWConfined.bind_readOnly_eq
    (rw_meta_to_direct (rw_readParam (pBase_in_readMeta (by decide)))) rfl h11 ?_
  refine RWConfined.ite_prog (fun hb => ?_) (fun _ => RWConfined.pure_prog _)
  refine rw_bind_direct htr (rw_meta_to_direct (rw_fastReadBktLane htr)) fun _ h1 _ => ?_
  refine rw_bind_direct h1 (rw_meta_to_direct (rw_fastReadBktLane h1)) fun s2 h2 _ => ?_
  unfold fastCheckBTreeFpProg
  refine RWConfined.ite_prog (fun hrole => ?_) (fun _ => RWConfined.pure_prog _)
  have hsr : RWConfined (FastReadDirect fl) fl.OwnsFastAddr s2
      (readParamPairProg (fl.pBase, (9, 2))) :=
    rw_meta_to_direct
      (RWConfined.of_readOnly (fun _ => rfl) ((cf_readParamPair (by decide) (by decide)).res_eq s2))
  refine rw_bind_direct h2 hsr fun _ h3 ⟨_, _⟩ => ?_
  refine RWConfined.ite_prog (fun _ => ?_) (fun _ => RWConfined.pure_prog _)
  refine rw_bind_direct h3 (rw_meta_to_direct (rw_fastFpHash h3)) fun s4 h4 _ => ?_
  refine RWConfined.ite_prog (fun _ => ?_) (fun _ => RWConfined.pure_prog _)
  unfold fastCheckBTreeSliceProg
  refine RWConfined.bind_readOnly_eq (rw_meta_to_direct rw_loadBTreeSliceCtx)
    (clientState_loadBTreeSliceCtxProg _ s4) (clientResult_loadBTreeSliceCtxProg h4.pt) ?_
  refine rw_bind_direct h4
    (rw_meta_to_direct (RWConfined.of_confined
      (confinedTo_btreeLookupBoundedProg (btreeSliceConf_fast h4.valid hb hrole))
      (fun _ h => h) writeMeta_sub_readMeta))
    fun _ h5 ⟨_, _⟩ => ?_
  refine RWConfined.ite_prog (fun _ => ?_) (fun _ => RWConfined.pure_prog _)
  refine rw_bind_direct h5 (rw_fastBpReadAt_direct h5 hup) fun _ _ _ => ?_
  exact RWConfined.ite_prog (fun _ => RWConfined.pure_prog _) (fun _ => RWConfined.pure_prog _)

private theorem rw_fastProbe_direct {w : ℕ} {fl : FastEpochLayout} {u_val : ℕ}
    {s : Memory.State} (htr : FastTableReady w fl s) (hup : fl.io.usePaged = 0) :
    RWConfined (FastReadDirect fl) fl.OwnsFastAddr s (fastProbeProg (fl.pBase, u_val)) := by
  have htail : ∀ st, FastTableReady w fl st → ∀ bq coll,
      RWConfined (FastReadDirect fl) fl.OwnsFastAddr st
        (fastProbeBTreeTailProg ((fl.pBase, u_val), (bq, coll))) := fun st hst ⟨_, _⟩ _ => by
    unfold fastProbeBTreeTailProg
    refine rw_bind_direct hst (rw_fastCheckBTree_direct hst hup) fun _ _ ⟨_, _⟩ => ?_
    exact RWConfined.ite_prog (fun _ => RWConfined.pure_prog _) (fun _ => RWConfined.pure_prog _)
  unfold fastProbeProg
  refine rw_bind_direct htr (rw_meta_to_direct (rw_fastFeistelSplit htr)) fun _ h1 _ => ?_
  refine rw_bind_direct h1 (rw_meta_to_direct (rw_fastRKey h1)) fun _ h2 _ => ?_
  refine rw_bind_direct h2 (rw_meta_to_direct (rw_fastReadMeta h2)) fun _ h3 _ => ?_
  refine RWConfined.ite_prog (fun hcr => ?_) (fun _ => RWConfined.pure_prog _)
  refine rw_bind_direct h3 (rw_fastCheckTrieRole_direct h3 hup hcr)
    fun _ h4 ⟨_, ⟨_, _⟩⟩ => ?_
  refine RWConfined.ite_prog (fun _ => RWConfined.pure_prog _) fun _ => ?_
  unfold fastProbeMissCurProg
  refine rw_bind_direct h4 (rw_meta_to_direct (rw_fastReadMeta h4)) fun _ h5 _ => ?_
  refine rw_bind_direct h5
    (rw_meta_to_direct (rw_readParam (pBase_in_readMeta (by decide)))) fun s6 h6 _ => ?_
  refine RWConfined.ite_prog (fun _ => ?_) (fun _ => htail s6 h6 _ _)
  simp only [pure_bind]
  refine rw_bind_direct h6 (rw_fastCheckTrieRole_direct h6 hup (by omega))
    fun s7 h7 ⟨_, ⟨_, _⟩⟩ => ?_
  exact RWConfined.ite_prog (fun _ => RWConfined.pure_prog _) fun _ =>
    RWConfined.ite_prog (fun _ => htail s7 h7 _ 1) fun _ =>
    RWConfined.ite_prog (fun _ => htail s7 h7 _ 1) (fun _ => htail s7 h7 _ 0)

private theorem rw_fastShadowStep_direct {w : ℕ} {fl : FastEpochLayout} {b : ℕ}
    {s : Memory.State} (htr : FastTableReady w fl s) (hup : fl.io.usePaged = 0) :
    RWConfined (FastReadDirect fl) fl.OwnsFastAddr s (fastShadowStepProg (fl.pBase, b)) := by
  have hcommit : ∀ st sr si, FastTableReady w fl st →
      RWConfined (FastReadDirect fl) fl.OwnsFastAddr st
        (fastCommitShadowProg (fl.pBase, (b, (sr, si)))) := fun _ _ _ hst => by
    refine rw_meta_to_direct ?_
    unfold fastCommitShadowProg
    refine rw_bind_meta hst (rw_fastWriteBktLane hst) fun _ h1 _ => ?_
    refine rw_bind_meta h1 (rw_fastWriteBktLane h1) fun _ h2 _ => ?_
    refine rw_bind_meta h2 (rw_fastWriteBktLane h2) fun _ h3 _ => ?_
    exact rw_fastWriteBktLane h3
  have hadv : ∀ st sp cnt sr si, FastTableReady w fl st →
      RWConfined (FastReadDirect fl) fl.OwnsFastAddr st
        (fastShadowAdvanceProg ((fl.pBase, b), ((sp, cnt), (sr, si)))) :=
    fun _ sp _ sr si hst => by
      unfold fastShadowAdvanceProg
      refine rw_bind_direct hst
        (rw_meta_to_direct (rw_readParam (pBase_in_readMeta (by decide)))) fun s1 h1 _ => ?_
      refine RWConfined.ite_prog (fun _ => RWConfined.ite_prog (fun _ =>
        RWConfined.ite_prog (fun _ => ?_) (fun _ => hcommit s1 sr si h1))
        (fun _ => hcommit s1 sr si h1)) (fun _ => hcommit s1 sr si h1)
      refine rw_meta_to_direct ?_
      refine rw_bind_meta h1 (rw_fastWriteBktLane h1) fun _ h2 _ => ?_
      exact rw_fastWriteBktLane h2
  unfold fastShadowStepProg
  refine rw_bind_direct htr
    (rw_meta_to_direct (rw_readParam (pBase_in_readMeta (by decide)))) fun _ h1 _ => ?_
  refine rw_bind_direct h1 (rw_meta_to_direct (rw_fastReadBktLane h1)) fun _ h2 _ => ?_
  refine RWConfined.ite_prog (fun _ => ?_) (fun _ => RWConfined.pure_prog _)
  refine rw_bind_direct h2 (rw_meta_to_direct (rw_fastReadBktCnt h2)) fun _ h3 _ => ?_
  unfold fastShadowBodyProg
  refine rw_bind_direct h3
    (rw_meta_to_direct (rw_readParam (pBase_in_readMeta (by decide)))) fun _ h4 _ => ?_
  refine RWConfined.ite_prog (fun _ => ?_) (fun _ => RWConfined.pure_prog _)
  refine rw_bind_direct h4 (rw_fastBpReadAt_direct h4 hup) fun _ h5 ⟨_, _⟩ => ?_
  refine rw_bind_direct h5 (rw_meta_to_direct (rw_fastFeistelRecon h5)) fun _ h6 _ => ?_
  refine rw_bind_direct h6 (rw_meta_to_direct (rw_fastReadBktLane h6)) fun _ h7 _ => ?_
  refine rw_bind_direct h7 (rw_meta_to_direct (rw_fastFpHash h7)) fun _ h8 _ => ?_
  unfold fastShadowBodyTailProg
  refine rw_bind_direct h8
    (rw_meta_to_direct (rw_readParam (pBase_in_readMeta (by decide)))) fun _ h9 _ => ?_
  refine rw_bind_direct h9 (rw_meta_to_direct (rw_fastReadBktLane h9)) fun _ h10 _ => ?_
  refine rw_bind_direct h10 (rw_meta_to_direct (rw_fastBTreeLookup h10)) fun s11 h11 ⟨_, _⟩ => ?_
  refine rw_bind_direct h11 (rw_meta_to_direct (rw_shadowRole fl _ s11)) fun _ h12 _ => ?_
  refine rw_bind_direct h12 (rw_meta_to_direct (rw_fastReadBktLane h12)) fun s13 h13 _ => ?_
  refine RWConfined.ite_prog (fun _ => ?_) (fun _ => hadv s13 _ _ _ _ h13)
  refine rw_bind_direct h13 (rw_meta_to_direct (rw_fastBTreeInsert h13)) fun s14 h14 _ => ?_
  exact hadv s14 _ _ _ _ h14

private theorem rw_fastShadowSteps8_direct {w : ℕ} {fl : FastEpochLayout} {b : ℕ}
    {s : Memory.State} (htr : FastTableReady w fl s) (hup : fl.io.usePaged = 0) :
    RWConfined (FastReadDirect fl) fl.OwnsFastAddr s (fastShadowSteps8Prog (fl.pBase, b)) := by
  have h2 : ∀ st, FastTableReady w fl st →
      RWConfined (FastReadDirect fl) fl.OwnsFastAddr st (fastShadowSteps2Prog (fl.pBase, b)) :=
    fun _ hst => by
      unfold fastShadowSteps2Prog
      exact rw_bind_direct hst (rw_fastShadowStep_direct hst hup)
        fun _ h1 _ => rw_fastShadowStep_direct h1 hup
  have h4 : ∀ st, FastTableReady w fl st →
      RWConfined (FastReadDirect fl) fl.OwnsFastAddr st (fastShadowSteps4Prog (fl.pBase, b)) :=
    fun st hst => by
      unfold fastShadowSteps4Prog
      exact rw_bind_direct hst (h2 st hst) fun s1 h1 _ => h2 s1 h1
  unfold fastShadowSteps8Prog
  exact rw_bind_direct htr (h4 s htr) fun s1 h1 _ => h4 s1 h1

private theorem rw_drainTryCheckDp_direct {w : ℕ} {fl : FastEpochLayout}
    {s : Memory.State} (htr : FastTableReady w fl s) (hup : fl.io.usePaged = 0) :
    RWConfined (FastReadDirect fl) fl.OwnsFastAddr s (drainTryCheckDpProg fl.pBase) := by
  unfold drainTryCheckDpProg
  refine rw_bind_direct htr (rw_meta_to_direct (rw_fastReadMeta htr)) fun _ h1 _ => ?_
  refine rw_bind_direct h1 (rw_meta_to_direct (rw_fastReadMeta h1)) fun _ h2 _ => ?_
  refine rw_bind_direct h2 (rw_meta_to_direct (rw_fastReadMeta h2)) fun _ h3 _ => ?_
  refine rw_bind_direct h3 (rw_meta_to_direct (rw_fastReadMeta h3)) fun _ h4 _ => ?_
  refine RWConfined.ite_prog (fun _ => ?_) (fun _ => RWConfined.pure_prog _)
  refine rw_bind_direct h4 (rw_meta_to_direct (rw_fastBufCheckSlot h4))
    fun _ h5 ⟨_, ⟨_, _⟩⟩ => ?_
  refine RWConfined.ite_prog (fun _ => ?_) (fun _ => RWConfined.pure_prog _)
  unfold drainTryCheckDpInnerProg
  refine rw_bind_direct h5 (rw_meta_to_direct (rw_fastReadBktCnt h5)) fun _ h6 _ => ?_
  refine RWConfined.ite_prog (fun _ => ?_) (fun _ => RWConfined.pure_prog _)
  refine rw_bind_direct h6 (rw_fastBpReadAt_direct h6 hup) fun _ h7 ⟨_, _⟩ => ?_
  refine rw_bind_direct h7 (rw_meta_to_direct (rw_fastFeistelRecon h7)) fun _ h8 _ => ?_
  refine rw_bind_direct h8 (rw_meta_to_direct (rw_fastFpHash h8)) fun _ h9 _ => ?_
  refine rw_bind_direct h9 (rw_meta_to_direct (rw_fastReadBktLane h9)) fun s10 h10 _ => ?_
  refine rw_bind_direct h10 (rw_meta_to_direct (rw_tryRole fl _ s10)) fun _ h11 _ => ?_
  refine rw_bind_direct h11 (rw_meta_to_direct (rw_fastBTreeLookup h11)) fun _ _ ⟨_, _⟩ => ?_
  exact RWConfined.pure_prog _

private theorem rw_drainTryStep_direct {w : ℕ} {fl : FastEpochLayout}
    {s : Memory.State} (htr : FastTableReady w fl s) (hup : fl.io.usePaged = 0) :
    RWConfined (FastReadDirect fl) fl.OwnsFastAddr s (drainTryStepProg fl.pBase) := by
  unfold drainTryStepProg
  refine rw_bind_direct htr (rw_meta_to_direct (rw_fastReadMeta htr)) fun _ h1 _ => ?_
  refine rw_bind_direct h1 (rw_meta_to_direct (rw_fastReadMeta h1)) fun _ h2 _ => ?_
  refine rw_bind_direct h2
    (rw_meta_to_direct (rw_readParam (pBase_in_readMeta (by decide)))) fun _ h3 _ => ?_
  refine RWConfined.ite_prog (fun _ => ?_) (fun _ => RWConfined.pure_prog _)
  refine rw_bind_direct h3 (rw_meta_to_direct (rw_fastReadBktCnt h3)) fun _ h4 _ => ?_
  refine rw_bind_direct h4 (rw_meta_to_direct (rw_fastReadMeta h4)) fun _ h5 _ => ?_
  refine RWConfined.ite_prog (fun _ => ?_) (fun _ => ?_)
  · unfold drainTryScanSlotProg
    refine rw_bind_direct h5 (rw_fastBpReadAt_direct h5 hup) fun _ h6 ⟨_, _⟩ => ?_
    refine rw_bind_direct h6 (rw_meta_to_direct (rw_fastFeistelRecon h6)) fun _ h7 _ => ?_
    refine rw_bind_direct h7 (rw_meta_to_direct (rw_fastReadBktLane h7)) fun _ h8 _ => ?_
    refine rw_bind_direct h8 (rw_meta_to_direct (rw_fastReadBktLane h8)) fun _ h9 _ => ?_
    refine rw_bind_direct h9 (rw_meta_to_direct (rw_fastFpHash h9)) fun _ h10 _ => ?_
    refine rw_bind_direct h10 (rw_meta_to_direct (rw_fastBTreeLookup h10)) fun _ h11 ⟨_, _⟩ => ?_
    refine RWConfined.ite_prog (fun _ => ?_) fun _ => ?_
    · refine rw_meta_to_direct ?_
      unfold drainTryInsertOrAdvProg
      refine rw_bind_meta h11 (rw_fastReadMeta h11) fun _ ha1 _ => ?_
      refine rw_bind_meta ha1 (rw_fastFpHash ha1) fun sa2 ha2 _ => ?_
      refine rw_bind_meta ha2 (rw_tryRole fl _ sa2) fun _ ha3 _ => ?_
      refine rw_bind_meta ha3 (rw_fastBTreeLookup ha3) fun _ ha4 ⟨_, _⟩ => ?_
      refine RWConfined.ite_prog (fun _ => rw_advanceTrySalt ha4) fun _ => ?_
      refine rw_bind_meta ha4 (rw_fastReadMeta ha4) fun _ ha5 _ => ?_
      refine rw_bind_meta ha5 (rw_readParam (pBase_in_readMeta (by decide))) fun _ ha6 _ => ?_
      refine RWConfined.ite_prog (fun _ => ?_) (fun _ => RWConfined.pure_prog _)
      refine rw_bind_meta ha6 (rw_fastBTreeInsert ha6) fun _ ha7 _ => ?_
      refine rw_bind_meta ha7 (rw_fastWriteMeta ha7) fun _ ha8 _ => ?_
      exact rw_fastWriteMeta ha8
    · refine rw_bind_direct h11
        (rw_meta_to_direct (rw_readParam (pBase_in_readMeta (by decide)))) fun _ hb1 _ => ?_
      exact RWConfined.ite_prog (fun _ => rw_meta_to_direct (rw_fastWriteMeta hb1))
        (fun _ => RWConfined.pure_prog _)
  · refine rw_bind_direct h5 (rw_drainTryCheckDp_direct h5 hup) fun _ h6 _ => ?_
    exact RWConfined.ite_prog
      (fun _ => rw_meta_to_direct (rw_commitTrySalt h6))
      (fun _ => rw_meta_to_direct (rw_advanceTrySalt h6))

private theorem rw_drainOldShadowMaint {w : ℕ} {fl : FastEpochLayout} {b fp loc cnt : ℕ}
    {s : Memory.State} (htr : FastTableReady w fl s) :
    RWConfined (FastReadMeta fl) (FastWriteMeta fl) s
      (drainOldShadowMaintProg (((fl.pBase, b), (fp, loc)), cnt)) := by
  unfold drainOldShadowMaintProg
  refine rw_bind_meta htr (rw_fastReadBktLane htr) fun _ h1 _ => ?_
  refine rw_bind_meta h1 (rw_fastReadBktLane h1) fun s2 h2 _ => ?_
  refine rw_bind_meta h2 (rw_shadowRole fl _ s2) fun _ h3 _ => ?_
  refine RWConfined.ite_prog (fun _ => ?_) fun _ => ?_
  · refine rw_bind_meta h3 (rw_readParam (pBase_in_readMeta (by decide))) fun _ h4 _ => ?_
    refine RWConfined.ite_prog (fun _ => ?_) (fun _ => RWConfined.pure_prog _)
    refine rw_bind_meta h4 (rw_fastBTreeReset h4) fun _ h5 _ => ?_
    refine rw_bind_meta h5 (rw_fastWriteBktLane h5) fun _ h6 _ => ?_
    exact rw_fastWriteBktLane h6
  · refine rw_bind_meta h3 (rw_readParam (pBase_in_readMeta (by decide))) fun _ h4 _ => ?_
    refine RWConfined.ite_prog (fun _ => RWConfined.ite_prog (fun _ => ?_)
      (fun _ => RWConfined.pure_prog _)) (fun _ => RWConfined.pure_prog _)
    refine rw_bind_meta h4 (rw_fastReadBktLane h4) fun _ h5 _ => ?_
    refine RWConfined.ite_prog (fun _ => ?_) (fun _ => RWConfined.pure_prog _)
    refine rw_bind_meta h5 (rw_fastBTreeInsert h5) fun _ h6 _ => ?_
    exact rw_fastWriteBktLane h6

private theorem rw_drainOldSlot_direct {w : ℕ} {fl : FastEpochLayout}
    {s : Memory.State} (htr : FastTableReady w fl s) (hup : fl.io.usePaged = 0) :
    RWConfined (FastReadDirect fl) fl.OwnsFastAddr s (drainOldSlotProg fl.pBase) := by
  unfold drainOldSlotProg
  refine rw_bind_direct htr (rw_meta_to_direct (rw_fastReadMeta htr)) fun _ h1 _ => ?_
  refine rw_bind_direct h1 (rw_meta_to_direct (rw_fastReadMeta h1)) fun _ h2 _ => ?_
  refine rw_bind_direct h2
    (rw_meta_to_direct (rw_readParam (pBase_in_readMeta (by decide)))) fun _ h3 _ => ?_
  refine RWConfined.ite_prog (fun _ => ?_) (fun _ => RWConfined.pure_prog _)
  simp only [pure_bind]
  refine rw_bind_direct h3 (rw_meta_to_direct (rw_fastBufItemAlloc h3)) fun _ h4 _ => ?_
  refine RWConfined.ite_prog (fun _ => ?_) (fun _ => RWConfined.pure_prog _)
  refine rw_bind_direct h4 (rw_meta_to_direct (rw_fastBufCheckSlot h4))
    fun _ h5 ⟨_, ⟨b, loc⟩⟩ => ?_
  refine RWConfined.ite_prog (fun _ => rw_meta_to_direct (rw_fastWriteMeta h5)) fun _ => ?_
  refine rw_bind_direct h5 (rw_fastShadowSteps8_direct (b := b) h5 hup) fun _ h6 _ => ?_
  unfold drainOldActiveBodyProg
  refine rw_bind_direct h6 (rw_meta_to_direct (rw_fastReadBktCnt h6)) fun _ h7 _ => ?_
  refine rw_bind_direct h7
    (rw_meta_to_direct (rw_readParam (pBase_in_readMeta (by decide)))) fun _ h8 _ => ?_
  refine RWConfined.ite_prog (fun _ => ?_) (fun _ => RWConfined.pure_prog _)
  refine rw_bind_direct h8 (rw_fastBpReadAt_direct h8 hup) fun _ h9 ⟨_, _⟩ => ?_
  refine rw_bind_direct h9 (rw_meta_to_direct (rw_fastFeistelRecon h9)) fun _ h10 _ => ?_
  refine rw_bind_direct h10 (rw_meta_to_direct (rw_fastRKey h10)) fun _ h11 _ => ?_
  refine rw_bind_direct h11 (rw_meta_to_direct (rw_fastReadBktLane h11)) fun _ h12 _ => ?_
  refine rw_bind_direct h12 (rw_meta_to_direct (rw_fastReadBktLane h12)) fun _ h13 _ => ?_
  refine rw_bind_direct h13 (rw_meta_to_direct (rw_fastFpHash h13)) fun _ h14 _ => ?_
  refine rw_bind_direct h14 (rw_meta_to_direct (rw_fastBTreeLookup h14)) fun _ h15 ⟨_, _⟩ => ?_
  refine RWConfined.ite_prog (fun _ => ?_) fun _ => ?_
  · refine rw_meta_to_direct ?_
    unfold drainOldInsertNoCollProg
    refine rw_bind_meta h15 (rw_fastReadBktLane h15) fun _ ha1 _ => ?_
    refine rw_bind_meta ha1 (rw_fastReadBktLane ha1) fun _ ha2 _ => ?_
    refine rw_bind_meta ha2 (rw_readParam (pBase_in_readMeta (by decide))) fun _ ha3 _ => ?_
    refine rw_bind_meta ha3 (rw_readParam (pBase_in_readMeta (by decide))) fun _ ha4 _ => ?_
    refine RWConfined.ite_prog (fun _ => ?_) (fun _ => RWConfined.pure_prog _)
    refine rw_bind_meta ha4 (rw_fastBTreeInsert ha4) fun _ ha5 _ => ?_
    refine rw_bind_meta ha5 (rw_fastWriteBktLane ha5) fun _ ha6 _ => ?_
    refine rw_bind_meta ha6 (rw_drainOldShadowMaint ha6) fun _ ha7 _ => ?_
    refine rw_bind_meta ha7 (rw_fastBufDelete ha7) fun _ ha8 _ => ?_
    exact rw_fastWriteMeta ha8
  · refine rw_bind_direct h15 (rw_meta_to_direct (rw_fastReadBktLane h15)) fun _ hb1 _ => ?_
    exact RWConfined.ite_prog (fun _ => rw_meta_to_direct (rw_startTrySalt hb1))
      (fun _ => RWConfined.pure_prog _)

private theorem rw_drainTrySteps5_direct {w : ℕ} {fl : FastEpochLayout}
    {s : Memory.State} (htr : FastTableReady w fl s) (hup : fl.io.usePaged = 0) :
    RWConfined (FastReadDirect fl) fl.OwnsFastAddr s (drainTrySteps5Prog fl.pBase) := by
  have h1 : ∀ st, FastTableReady w fl st →
      RWConfined (FastReadDirect fl) fl.OwnsFastAddr st (drainTryTickProg fl.pBase) :=
    fun _ hst => by
      unfold drainTryTickProg
      refine rw_bind_direct hst (rw_meta_to_direct (rw_fastReadMeta hst)) fun _ ha1 _ => ?_
      refine RWConfined.ite_prog (fun _ => ?_) (fun _ => RWConfined.pure_prog _)
      refine rw_bind_direct ha1 (rw_drainTryStep_direct ha1 hup) fun _ ha2 _ => ?_
      refine rw_bind_direct ha2 (rw_meta_to_direct (rw_fastReadMeta ha2)) fun _ ha3 _ => ?_
      exact RWConfined.ite_prog (fun _ => rw_drainOldSlot_direct ha3 hup)
        (fun _ => RWConfined.pure_prog _)
  unfold drainTrySteps5Prog
  refine rw_bind_direct htr (h1 s htr) fun s1 hr1 _ => ?_
  refine rw_bind_direct hr1 (h1 s1 hr1) fun s2 hr2 _ => ?_
  refine rw_bind_direct hr2 (h1 s2 hr2) fun s3 hr3 _ => ?_
  refine rw_bind_direct hr3 (h1 s3 hr3) fun s4 hr4 _ => ?_
  exact h1 s4 hr4

private theorem rw_advanceSubEpoch_direct {w : ℕ} {fl : FastEpochLayout}
    {s : Memory.State} (htr : FastTableReady w fl s) (hup : fl.io.usePaged = 0) :
    RWConfined (FastReadDirect fl) fl.OwnsFastAddr s (advanceSubEpochProg fl.pBase) := by
  have htick : ∀ st, FastTableReady w fl st →
      RWConfined (FastReadDirect fl) fl.OwnsFastAddr st (drainTickProg fl.pBase) :=
    fun _ hst => by
      unfold drainTickProg
      refine rw_bind_direct hst (rw_meta_to_direct (rw_fastReadMeta hst)) fun _ ha1 _ => ?_
      refine RWConfined.ite_prog (fun _ => ?_) (fun _ => rw_drainOldSlot_direct ha1 hup)
      refine rw_bind_direct ha1 (rw_drainTryStep_direct ha1 hup) fun _ ha2 _ => ?_
      refine rw_bind_direct ha2 (rw_meta_to_direct (rw_fastReadMeta ha2)) fun _ ha3 _ => ?_
      exact RWConfined.ite_prog (fun _ => rw_drainOldSlot_direct ha3 hup)
        (fun _ => RWConfined.pure_prog _)
  have h2 : ∀ st, FastTableReady w fl st →
      RWConfined (FastReadDirect fl) fl.OwnsFastAddr st (drainTicks2Prog fl.pBase) :=
    fun st hst => by
      unfold drainTicks2Prog
      exact rw_bind_direct hst (htick st hst) fun s1 hr1 _ => htick s1 hr1
  have h4 : ∀ st, FastTableReady w fl st →
      RWConfined (FastReadDirect fl) fl.OwnsFastAddr st (drainTicks4Prog fl.pBase) :=
    fun st hst => by
      unfold drainTicks4Prog
      exact rw_bind_direct hst (h2 st hst) fun s1 hr1 _ => h2 s1 hr1
  have h8 : ∀ st, FastTableReady w fl st →
      RWConfined (FastReadDirect fl) fl.OwnsFastAddr st (drainTicks8Prog fl.pBase) :=
    fun st hst => by
      unfold drainTicks8Prog
      exact rw_bind_direct hst (h4 st hst) fun s1 hr1 _ => h4 s1 hr1
  have h16 : ∀ st, FastTableReady w fl st →
      RWConfined (FastReadDirect fl) fl.OwnsFastAddr st (drainTicks16Prog fl.pBase) :=
    fun st hst => by
      unfold drainTicks16Prog
      exact rw_bind_direct hst (h8 st hst) fun s1 hr1 _ => h8 s1 hr1
  unfold advanceSubEpochProg
  refine rw_bind_direct htr (rw_meta_to_direct (rw_fastReadMeta htr)) fun _ hr1 _ => ?_
  refine rw_bind_direct hr1
    (rw_meta_to_direct (rw_readParam (pBase_in_readMeta (by decide)))) fun s2 hr2 _ => ?_
  simp only [pure_bind]
  refine RWConfined.ite_prog (fun _ => ?_) fun _ => ?_
  · refine rw_bind_direct hr2 (h16 s2 hr2) fun _ hr3 _ => ?_
    refine RWConfined.ite_prog (fun _ => rw_meta_to_direct (rw_fastWriteMeta hr3)) fun _ => ?_
    refine rw_bind_direct hr3 (rw_meta_to_direct (rw_fastReadMeta hr3)) fun _ hr4 _ => ?_
    refine RWConfined.ite_prog (fun _ => ?_) (fun _ => RWConfined.pure_prog _)
    refine rw_bind_direct hr4 (rw_meta_to_direct (rw_fastBufItemAlloc hr4)) fun _ hr5 _ => ?_
    refine rw_bind_direct hr5 (rw_meta_to_direct (rw_fastReadMeta hr5)) fun _ hr6 _ => ?_
    refine rw_bind_direct hr6 (rw_meta_to_direct (rw_fastReadMeta hr6)) fun _ hr7 _ => ?_
    exact RWConfined.ite_prog
      (fun _ => rw_meta_to_direct (rw_fastWriteMeta hr7))
      (fun _ => rw_fastEnterFallback_direct hr7 hup)
  · refine rw_meta_to_direct ?_
    refine rw_bind_meta hr2 (rw_fastReadMeta hr2) fun _ hb1 _ => ?_
    refine RWConfined.ite_prog (fun _ => ?_) (fun _ => RWConfined.pure_prog _)
    refine rw_bind_meta hb1 (rw_fastBufClearSteps hb1) fun _ hb2 _ => ?_
    refine RWConfined.ite_prog (fun _ => rw_fastWriteMeta hb2) fun _ => ?_
    refine rw_bind_meta hb2 (rw_fastWriteMeta hb2) fun _ hb3 _ => ?_
    refine rw_bind_meta hb3 (rw_fastWriteMeta hb3) fun _ hb4 _ => ?_
    exact rw_fastWriteMeta hb4

private theorem rw_fastCheckRKeyFree {w : ℕ} {fl : FastEpochLayout} {u_val : ℕ}
    {s : Memory.State} (htr : FastTableReady w fl s) :
    RWConfined (FastReadMeta fl) (FastWriteMeta fl) s
      (fastCheckRKeyFreeProg (fl.pBase, u_val)) := by
  unfold fastCheckRKeyFreeProg
  refine rw_bind_meta htr (rw_fastRKey htr) fun _ h1 _ => ?_
  refine rw_bind_meta h1 (rw_fastReadMeta h1) fun _ h2 _ => ?_
  refine RWConfined.ite_prog (fun _ => ?_) (fun _ => RWConfined.pure_prog _)
  refine rw_bind_meta h2 (rw_fastBufLookup h2) fun _ h3 _ => ?_
  refine RWConfined.ite_prog (fun _ => RWConfined.pure_prog _) fun _ => ?_
  refine rw_bind_meta h3 (rw_fastReadMeta h3) fun _ h4 _ => ?_
  refine rw_bind_meta h4 (rw_readParam (pBase_in_readMeta (by decide))) fun _ h5 _ => ?_
  refine RWConfined.ite_prog (fun _ => ?_) (fun _ => RWConfined.pure_prog _)
  refine rw_bind_meta h5 (rw_fastBufLookup h5) fun _ _ _ => ?_
  exact RWConfined.ite_prog (fun _ => RWConfined.pure_prog _) (fun _ => RWConfined.pure_prog _)

private theorem rw_fastInsertNewStep_direct {w : ℕ} {fl : FastEpochLayout}
    {u_val b cnt v_val : ℕ} {s : Memory.State}
    (htr : FastTableReady w fl s) (hup : fl.io.usePaged = 0) :
    RWConfined (FastReadDirect fl) fl.OwnsFastAddr s
      (fastInsertNewStepProg ((fl.pBase, u_val), ((b, cnt), v_val))) := by
  unfold fastInsertNewStepProg
  refine rw_bind_direct htr (rw_drainTrySteps5_direct htr hup) fun _ h1 _ => ?_
  refine rw_bind_direct h1 (rw_fastShadowSteps8_direct (b := b) h1 hup) fun _ h2 _ => ?_
  refine rw_bind_direct h2 (rw_meta_to_direct (rw_fastFeistelSplit h2)) fun _ h3 ⟨_, _⟩ => ?_
  refine rw_bind_direct h3 (rw_fastBpAppend_direct h3 hup) fun _ h4 _ => ?_
  refine rw_bind_direct h4 (rw_meta_to_direct (rw_fastRKey h4)) fun _ h5 _ => ?_
  refine rw_bind_direct h5 (rw_meta_to_direct (rw_fastReadMeta h5)) fun _ h6 _ => ?_
  exact rw_meta_to_direct (rw_fastBufInsert h6)

private theorem rw_fastInsert_direct {w : ℕ} {fl : FastEpochLayout} {u_val v_val : ℕ}
    {s : Memory.State} (htr : FastTableReady w fl s) (hup : fl.io.usePaged = 0) :
    RWConfined (FastReadDirect fl) (FastReadDirect fl) s
      (fastInsertProg ((fl.pBase, u_val), v_val)) := by
  have liftD : ∀ {α : Type} {st : Memory.State} {p : Memory.Prog α},
      RWConfined (FastReadDirect fl) fl.OwnsFastAddr st p →
      RWConfined (FastReadDirect fl) (FastReadDirect fl) st p :=
    fun hp => hp.mono ownsFast_sub_readDirect (fun _ h => h) ownsFast_sub_readDirect
  have bindD : ∀ {α β : Type} {st : Memory.State} {p : Memory.Prog α} {q : α → Memory.Prog β},
      FastTableReady w fl st →
      RWConfined (FastReadDirect fl) fl.OwnsFastAddr st p →
      (∀ s', FastTableReady w fl s' → ∀ r,
        RWConfined (FastReadDirect fl) (FastReadDirect fl) s' (q r)) →
      RWConfined (FastReadDirect fl) (FastReadDirect fl) st (p >>= q) :=
    fun hst hp hq => RWConfined.bind_prog (liftD hp) (hq _ (hst.step_direct hp) _)
  unfold fastInsertProg
  refine bindD htr (rw_fastProbe_direct htr hup) fun _ h1 ⟨⟨_, _⟩, ⟨_, ⟨_, _⟩⟩⟩ => ?_
  refine RWConfined.ite_prog (fun _ => ?_) fun _ => ?_
  · refine bindD h1 (rw_meta_to_direct (rw_fastFeistelSplit h1)) fun _ h2 ⟨_, _⟩ => ?_
    exact liftD (rw_fastBpWriteAt_direct h2 hup)
  · refine bindD h1 (rw_meta_to_direct (rw_fastCheckRKeyFree h1)) fun _ h2 _ => ?_
    refine RWConfined.ite_prog (fun _ => ?_) fun _ => ?_
    · exact bindD h2 (rw_fastEnterFallback_direct h2 hup)
        fun _ h3 _ => rw_fastFallbackInsert_direct h3 hup
    · refine bindD h2 (rw_meta_to_direct (rw_fastReadBktCnt h2)) fun _ h3 _ => ?_
      refine bindD h3 (rw_meta_to_direct (rw_readParam (pBase_in_readMeta (by decide))))
        fun _ h4 _ => ?_
      refine RWConfined.ite_prog (fun _ => ?_) fun _ => ?_
      · exact bindD h4 (rw_fastEnterFallback_direct h4 hup)
          fun _ h5 _ => rw_fastFallbackInsert_direct h5 hup
      · exact liftD (rw_bind_direct h4 (rw_fastInsertNewStep_direct h4 hup)
          fun _ h5 _ => rw_advanceSubEpoch_direct h5 hup)

private theorem rw_fastSwapLastDown_direct {w : ℕ} {fl : FastEpochLayout}
    {b delLoc lastLoc : ℕ} {s : Memory.State}
    (htr : FastTableReady w fl s) (hup : fl.io.usePaged = 0) :
    RWConfined (FastReadDirect fl) fl.OwnsFastAddr s
      (fastSwapLastDownProg ((fl.pBase, b), (delLoc, lastLoc))) := by
  unfold fastSwapLastDownProg
  refine RWConfined.ite_prog (fun _ => ?_) (fun _ => RWConfined.pure_prog _)
  refine rw_bind_direct htr (rw_fastBpReadAt_direct htr hup) fun _ h1 ⟨_, _⟩ => ?_
  refine rw_bind_direct h1 (rw_meta_to_direct (rw_fastFeistelRecon h1)) fun _ h2 _ => ?_
  refine rw_bind_direct h2 (rw_fastBpWriteAt_direct h2 hup) fun _ h3 _ => ?_
  exact rw_meta_to_direct (rw_fastRelocLast h3)

private theorem rw_fastRemoveAt_direct {w : ℕ} {fl : FastEpochLayout} {b delLoc u_val : ℕ}
    {s : Memory.State} (htr : FastTableReady w fl s) (hup : fl.io.usePaged = 0) :
    RWConfined (FastReadDirect fl) fl.OwnsFastAddr s
      (fastRemoveAtProg ((fl.pBase, b), (delLoc, u_val))) := by
  unfold fastRemoveAtProg
  refine rw_bind_direct htr
    (rw_meta_to_direct (rw_readParam (pBase_in_readMeta (by decide)))) fun _ h1 _ => ?_
  refine RWConfined.ite_prog (fun _ => ?_) (fun _ => RWConfined.pure_prog _)
  refine rw_bind_direct h1 (rw_meta_to_direct (rw_fastReadBktCnt h1)) fun _ h2 _ => ?_
  refine RWConfined.ite_prog (fun _ => ?_) (fun _ => RWConfined.pure_prog _)
  simp only [pure_bind]
  refine rw_bind_direct h2 (rw_meta_to_direct (rw_fastUnindexAt h2)) fun _ h3 _ => ?_
  refine rw_bind_direct h3 (rw_fastSwapLastDown_direct h3 hup) fun _ h4 _ => ?_
  refine rw_bind_direct h4 (rw_fastBpPopBktBack_direct h4 hup) fun _ h5 _ => ?_
  refine rw_bind_direct h5 (rw_meta_to_direct (rw_fastPromoteShadowIfDone h5)) fun _ h6 _ => ?_
  exact rw_meta_to_direct (rw_fastClampTryPos h6)

/-- Read/write word-address envelope of a direct-mode (`usePaged = 0`) epoch slot. -/
@[expose] def SlotDirectRegion (c w pBase metaBase nCap : ℕ) (io : SlotIoLayout) (addr : ℕ) :
    Prop :=
  (pBase ≤ addr ∧ addr < pBase + 64) ∨
  slotOwnsNonPageMeta c w metaBase nCap addr ∨
  io.OwnsAddr addr

private theorem cf_loadSmallIoCtx {R : ℕ → Prop} {pBase : ℕ}
    (hp : ∀ k < 64, R (pBase + k)) :
    ConfinedTo R (loadSmallIoCtxProg pBase) := by
  unfold loadSmallIoCtxProg
  refine ConfinedTo.bind_prog (ConfinedTo.read_prog (hp 48 (by decide))) fun _ =>
    ConfinedTo.bind_prog (ConfinedTo.read_prog (hp 49 (by decide))) fun _ =>
    ConfinedTo.bind_prog (ConfinedTo.read_prog (hp 50 (by decide))) fun _ =>
    ConfinedTo.bind_prog (ConfinedTo.read_prog (hp 51 (by decide))) fun _ =>
    ConfinedTo.bind_prog (ConfinedTo.read_prog (hp 52 (by decide))) fun _ =>
    ConfinedTo.bind_prog (ConfinedTo.read_prog (hp 53 (by decide))) fun _ =>
    ConfinedTo.bind_prog (ConfinedTo.read_prog (hp 54 (by decide))) fun _ =>
    ConfinedTo.bind_prog (ConfinedTo.read_prog (hp 55 (by decide))) fun _ =>
    ConfinedTo.bind_prog (ConfinedTo.read_prog (hp 56 (by decide))) fun _ =>
    ConfinedTo.bind_prog (ConfinedTo.read_prog (hp 57 (by decide))) fun _ =>
    ConfinedTo.bind_prog (ConfinedTo.read_prog (hp 58 (by decide))) fun _ =>
    ConfinedTo.bind_prog (ConfinedTo.read_prog (hp 59 (by decide))) fun _ =>
    ConfinedTo.bind_prog (ConfinedTo.read_prog (hp 60 (by decide))) fun _ =>
    ConfinedTo.pure_prog _

private theorem fastReadDirect_sub_slotDirect {c U V w pBase metaBase nCap : ℕ}
    {io : SlotIoLayout} (hne : nCap ≠ 0) (addr : ℕ)
    (ha : FastReadDirect ⟨c, U, V, w, nCap, metaBase, pBase, io⟩ addr) :
    SlotDirectRegion c w pBase metaBase nCap io addr := by
  rcases ha with (hp | h0 | h32) | hio
  · exact Or.inl hp
  · exact Or.inr (Or.inl (Or.inl ⟨h0.1, by simp only [hne, ↓reduceIte]; exact h0.2⟩))
  · exact Or.inr (Or.inl (Or.inr ⟨hne, h32⟩))
  · exact Or.inr (Or.inr hio)

/-- Direct-mode (`io.usePaged = 0`) `RWConfined` certificate for `epochInsertProg` on
`EpochSlotInv`. -/
theorem epochInsert_direct_rw {c U V w pBase metaBase u_val v_val : ℕ} {io : SlotIoLayout}
    {draining : Bool} {sl : SlotLatent c U V} {s₁ : Memory.State}
    (h : EpochSlotInv c U V w s₁.frontier pBase metaBase io 0 draining sl s₁.mem)
    (hup : io.usePaged = 0) :
    RWConfined (SlotDirectRegion c w pBase metaBase sl.nCap io)
      (SlotDirectRegion c w pBase metaBase sl.nCap io) s₁
      (epochInsertProg ((pBase, u_val), v_val)) := by
  set R := SlotDirectRegion c w pBase metaBase sl.nCap io
  have hp_in : ∀ k < 64, R (pBase + k) :=
    fun k hk => Or.inl ⟨Nat.le_add_right _ _, by omega⟩
  unfold epochInsertProg
  by_cases h0 : sl.nCap = 0
  · unfold EpochSlotInv at h; rw [ite_eq_left h0] at h
    obtain ⟨_, _, hv, hpt, _, _⟩ := h
    have ⟨hm0, hm1, _⟩ := hpt
    have hrd0 : (Memory.spec 0).clientResult s₁ (Memory.read pBase) = 0 := hm0
    have hrd1 : (Memory.spec 0).clientResult s₁ (Memory.read (pBase + 1)) = metaBase := hm1
    refine RWConfined.bind_readOnly_eq (RWConfined.read_prog (by simpa using hp_in 0 (by decide)))
      rfl hrd0 ?_
    rw [ite_eq_left rfl]
    refine RWConfined.bind_readOnly_eq (RWConfined.read_prog (hp_in 1 (by decide))) rfl hrd1 ?_
    refine RWConfined.bind_readOnly_eq
      (RWConfined.of_readOnly (clientState_loadSmallIoCtxProg pBase)
        ((cf_loadSmallIoCtx hp_in).res_eq s₁))
      (clientState_loadSmallIoCtxProg pBase s₁) (clientResult_loadSmallIoCtxProg hpt) ?_
    have hm_mb0 : R metaBase :=
      Or.inr (Or.inl (Or.inl ⟨le_rfl, by simp only [h0, ↓reduceIte]; omega⟩))
    have hm_mb1 : R (metaBase + 1) :=
      Or.inr (Or.inl (Or.inl ⟨by omega, by simp only [h0, ↓reduceIte]; omega⟩))
    have hioD : SlotIoDirectConf R io.toCtx := by
      dsimp only [SlotIoDirectConf]; rw [SlotIoLayout.ofCtx_toCtx]
      exact ⟨hup, hv.io_valid.w_pos, fun addr ha => Or.inr (Or.inr ha)⟩
    exact RWConfined.of_confined (confinedTo_smallEpochInsertRawProg hm_mb0 hm_mb1 hioD)
      (fun _ h => h) (fun _ h => h)
  · have htr : FastTableReady w ⟨c, U, V, w, sl.nCap, metaBase, pBase, io⟩ s₁ :=
      FastTableReady.of_ready (h.fastLayoutReady h0)
    have hrd0 : (Memory.spec 0).clientResult s₁ (Memory.read pBase) = sl.nCap := by
      change s₁.mem pBase = sl.nCap
      simpa [FastEpochLayout.paramWord] using htr.pt 0 (by decide)
    refine RWConfined.bind_readOnly_eq (RWConfined.read_prog (by simpa using hp_in 0 (by decide)))
      rfl hrd0 ?_
    rw [ite_eq_right h0]
    refine (?_ : RWConfined
      (FastReadDirect ⟨c, U, V, w, sl.nCap, metaBase, pBase, io⟩)
      (FastReadDirect ⟨c, U, V, w, sl.nCap, metaBase, pBase, io⟩) s₁
      (largeEpochInsertProg ((pBase, u_val), v_val))).mono
        (fun _ h => h) (fastReadDirect_sub_slotDirect h0) (fastReadDirect_sub_slotDirect h0)
    unfold largeEpochInsertProg
    have hrm : RWConfined (FastReadDirect ⟨c, U, V, w, sl.nCap, metaBase, pBase, io⟩)
        (FastReadDirect ⟨c, U, V, w, sl.nCap, metaBase, pBase, io⟩) s₁
        (fastReadMetaProg (pBase, 2)) :=
      (rw_fastReadMeta (off := 2) htr).mono writeMeta_sub_readMeta (fun _ => Or.inl)
        (fun a hw => Or.inl (writeMeta_sub_readMeta a hw))
    refine RWConfined.bind_readOnly hrm (clientState_fastReadMetaProg _ s₁) ?_
    exact RWConfined.ite_prog
      (fun _ => rw_fastInsert_direct htr hup)
      (fun _ => rw_fastFallbackInsert_direct htr hup)

/-- Direct-mode (`io.usePaged = 0`) `RWConfined` certificate for `epochDeleteProg` on
`EpochSlotInv`. -/
theorem epochDelete_direct_rw {c U V w pBase metaBase u_val : ℕ} {io : SlotIoLayout}
    {draining : Bool} {sl : SlotLatent c U V} {s₁ : Memory.State}
    (h : EpochSlotInv c U V w s₁.frontier pBase metaBase io 0 draining sl s₁.mem)
    (hup : io.usePaged = 0) :
    RWConfined (SlotDirectRegion c w pBase metaBase sl.nCap io)
      (SlotDirectRegion c w pBase metaBase sl.nCap io) s₁
      (epochDeleteProg (pBase, u_val)) := by
  set R := SlotDirectRegion c w pBase metaBase sl.nCap io
  have hp_in : ∀ k < 64, R (pBase + k) :=
    fun k hk => Or.inl ⟨Nat.le_add_right _ _, by omega⟩
  unfold epochDeleteProg
  by_cases h0 : sl.nCap = 0
  · unfold EpochSlotInv at h; rw [ite_eq_left h0] at h
    obtain ⟨_, _, hv, hpt, _, _⟩ := h
    have ⟨hm0, hm1, _⟩ := hpt
    have hrd0 : (Memory.spec 0).clientResult s₁ (Memory.read pBase) = 0 := hm0
    have hrd1 : (Memory.spec 0).clientResult s₁ (Memory.read (pBase + 1)) = metaBase := hm1
    refine RWConfined.bind_readOnly_eq (RWConfined.read_prog (by simpa using hp_in 0 (by decide)))
      rfl hrd0 ?_
    rw [ite_eq_left rfl]
    refine RWConfined.bind_readOnly_eq (RWConfined.read_prog (hp_in 1 (by decide))) rfl hrd1 ?_
    refine RWConfined.bind_readOnly_eq
      (RWConfined.of_readOnly (clientState_loadSmallIoCtxProg pBase)
        ((cf_loadSmallIoCtx hp_in).res_eq s₁))
      (clientState_loadSmallIoCtxProg pBase s₁) (clientResult_loadSmallIoCtxProg hpt) ?_
    have hm_mb0 : R metaBase :=
      Or.inr (Or.inl (Or.inl ⟨le_rfl, by simp only [h0, ↓reduceIte]; omega⟩))
    have hm_mb1 : R (metaBase + 1) :=
      Or.inr (Or.inl (Or.inl ⟨by omega, by simp only [h0, ↓reduceIte]; omega⟩))
    have hioD : SlotIoDirectConf R io.toCtx := by
      dsimp only [SlotIoDirectConf]; rw [SlotIoLayout.ofCtx_toCtx]
      exact ⟨hup, hv.io_valid.w_pos, fun addr ha => Or.inr (Or.inr ha)⟩
    exact RWConfined.of_confined (confinedTo_smallEpochDeleteRawProg hm_mb0 hm_mb1 hioD)
      (fun _ h => h) (fun _ h => h)
  · have htr : FastTableReady w ⟨c, U, V, w, sl.nCap, metaBase, pBase, io⟩ s₁ :=
      FastTableReady.of_ready (h.fastLayoutReady h0)
    have hrd0 : (Memory.spec 0).clientResult s₁ (Memory.read pBase) = sl.nCap := by
      change s₁.mem pBase = sl.nCap
      simpa [FastEpochLayout.paramWord] using htr.pt 0 (by decide)
    refine RWConfined.bind_readOnly_eq (RWConfined.read_prog (by simpa using hp_in 0 (by decide)))
      rfl hrd0 ?_
    rw [ite_eq_right h0]
    refine (?_ : RWConfined
      (FastReadDirect ⟨c, U, V, w, sl.nCap, metaBase, pBase, io⟩)
      (FastReadDirect ⟨c, U, V, w, sl.nCap, metaBase, pBase, io⟩) s₁
      (largeEpochDeleteProg (pBase, u_val))).mono
        (fun _ h => h) (fastReadDirect_sub_slotDirect h0) (fastReadDirect_sub_slotDirect h0)
    unfold largeEpochDeleteProg
    have hrm : RWConfined (FastReadDirect ⟨c, U, V, w, sl.nCap, metaBase, pBase, io⟩)
        (FastReadDirect ⟨c, U, V, w, sl.nCap, metaBase, pBase, io⟩) s₁
        (fastReadMetaProg (pBase, 2)) :=
      (rw_fastReadMeta (off := 2) htr).mono writeMeta_sub_readMeta (fun _ => Or.inl)
        (fun a hw => Or.inl (writeMeta_sub_readMeta a hw))
    refine RWConfined.bind_readOnly hrm (clientState_fastReadMetaProg _ s₁) ?_
    refine RWConfined.ite_prog (fun _ => ?_) (fun _ => rw_fastFallbackDelete_direct htr hup)
    unfold fastDeleteProg
    refine RWConfined.bind_prog
      ((rw_fastProbe_direct htr hup).mono ownsFast_sub_readDirect (fun _ h => h)
        ownsFast_sub_readDirect) ?_
    have htr' := htr.step_direct (rw_fastProbe_direct (u_val := u_val) htr hup)
    rcases (Memory.spec 0).clientResult s₁ (fastProbeProg (pBase, u_val)) with ⟨⟨_, _⟩, ⟨_, ⟨_, _⟩⟩⟩
    exact RWConfined.ite_prog
      (fun _ => RWConfined.pure_prog _)
      (fun _ => (rw_fastRemoveAt_direct htr' hup).mono
        ownsFast_sub_readDirect (fun _ h => h) ownsFast_sub_readDirect)

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

end
