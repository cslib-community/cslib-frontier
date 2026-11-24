/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeBTreeProg
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeTrieProg
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeBlockPoolMetaProg
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeBlockPoolStepProg
-- Retain private `import all` solely to unfold unexposed `Memory.Prog` bodies of the metadata stack
-- without modifying upstream modules or invalidating cached `.olean` artifacts.
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeMetaProg
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeBTreeBase
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeBTreeProg
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeTrieProg
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeBlockPoolMetaProg
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeBlockPoolStepProg
import Mathlib.Tactic.Ring

/-!
# Metadata Region Confinement (`ConfinedTo`) for Phase-`8` Migration Congruence

This module defines the state-free compositional confinement predicate `ConfinedTo M p` for
`Memory.Prog` programs whose reads and writes stay inside an address region `M : ℕ → Prop`, and
certifies `ConfinedTo` for the B+-tree (`LargeBTreeProg`), `BufTrie` (`LargeTrieProg`), and
block-pool metadata (`LargeBlockPoolMetaProg`, `LargeBlockPoolStepProg`) operations invoked when
draining a paged source slot during Phase `8` (`migrate`).

## Main definitions

* `ConfinedTo`: state-free region-confinement certificate bundling `clientResult` agreement on `M`,
  `frontier` preservation, post-state `M` agreement, and outside-`M` frame preservation.

## Main results

* `confinedTo_btreeLookupBoundedProg`,
  `confinedTo_btreeDeleteBoundedProg`, `confinedTo_btreeUpdateBoundedProg`,
  `confinedTo_btreeInsertBoundedProg`
* `confinedTo_bufLookupBoundedProg`, `confinedTo_bufDeleteBoundedProg`,
  `confinedTo_bufInsertBoundedProg`, `confinedTo_bufCheckSlotBoundedProg`,
  `confinedTo_bufClearStepsBoundedProg`
* `confinedTo_bpReadScalarProg`, `confinedTo_bpWriteScalarProg`,
  `confinedTo_bpReadTailDirRawProg`, `confinedTo_bpWriteTailDirRawProg`,
  `confinedTo_bpReadSlabOwnerProg`, `confinedTo_bpWriteSlabOwnerProg`,
  `confinedTo_bpPrepPopMetaProg`, `confinedTo_bpCommitPopMetaProg`,
  `confinedTo_bpBktTickMetaProg`, `confinedTo_bpTopCleanMetaProg`
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.WordRAM.Resizable
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct

/-! ## Section 1: State-Free `ConfinedTo` Combinators -/

/-- State-free region-confinement certificate for `p : Memory.Prog α`: `p` preserves `frontier`,
leaves addresses outside `M` untouched, and maps any two states agreeing on `M` to equal results
and post-states agreeing on `M`. -/
structure ConfinedTo {α : Type} (M : ℕ → Prop) (p : Memory.Prog α) : Prop where
  /-- `frontier` is preserved for every input state. -/
  fr_eq : ∀ s, ((Memory.spec 0).clientState s p).frontier = s.frontier
  /-- Every word address outside `M` is unchanged. -/
  mem_out : ∀ s addr, ¬M addr → ((Memory.spec 0).clientState s p).mem addr = s.mem addr
  /-- Any two states agreeing on `M` yield equal return values. -/
  res_eq : ∀ s₁ s₂, (∀ addr, M addr → s₁.mem addr = s₂.mem addr) →
    (Memory.spec 0).clientResult s₁ p = (Memory.spec 0).clientResult s₂ p
  /-- Any two states agreeing on `M` yield post-states agreeing on `M`. -/
  mem_in : ∀ s₁ s₂, (∀ addr, M addr → s₁.mem addr = s₂.mem addr) →
    ∀ addr, M addr →
      ((Memory.spec 0).clientState s₁ p).mem addr = ((Memory.spec 0).clientState s₂ p).mem addr

namespace ConfinedTo

/-- `pure x` is confined to any region `M`. -/
theorem pure_prog {α : Type} {M : ℕ → Prop} (x : α) : ConfinedTo M (pure x : Memory.Prog α) where
  fr_eq _ := rfl
  mem_out _ _ _ := rfl
  res_eq _ _ _ := rfl
  mem_in _ _ h _ ha := h _ ha

/-- Monotonicity of `ConfinedTo` in the address predicate `M`. -/
theorem mono {α : Type} {M₁ M₂ : ℕ → Prop} {p : Memory.Prog α}
    (hp : ConfinedTo M₁ p) (hsub : ∀ addr, M₁ addr → M₂ addr) :
    ConfinedTo M₂ p where
  fr_eq := hp.fr_eq
  mem_out s addr hnot := hp.mem_out s addr (fun h1 => hnot (hsub addr h1))
  res_eq s₁ s₂ h := hp.res_eq s₁ s₂ (fun addr ha => h addr (hsub addr ha))
  mem_in s₁ s₂ h addr ha := by
    by_cases h1 : M₁ addr
    · exact hp.mem_in s₁ s₂ (fun b hb => h b (hsub b hb)) addr h1
    · rw [hp.mem_out s₁ addr h1, hp.mem_out s₂ addr h1, h addr ha]

/-- `Memory.read a` is confined to `M` whenever `M a`. -/
theorem read_prog {M : ℕ → Prop} {a : ℕ} (ha : M a) : ConfinedTo M (Memory.read a) where
  fr_eq _ := rfl
  mem_out _ _ _ := rfl
  res_eq _ _ h := h a ha
  mem_in _ _ h _ hb := h _ hb

/-- `Memory.write a v` is confined to `M` whenever `M a`. -/
theorem write_prog {M : ℕ → Prop} {a : ℕ} (ha : M a) (v : ℕ) :
    ConfinedTo M (Memory.write a v) where
  fr_eq _ := rfl
  mem_out s addr hnot := by
    change Function.update s.mem a v addr = s.mem addr
    exact Function.update_of_ne (fun heq : addr = a => hnot (heq ▸ ha)) v s.mem
  res_eq _ _ _ := rfl
  mem_in s₁ s₂ h addr hb := by
    change Function.update s₁.mem a v addr = Function.update s₂.mem a v addr
    by_cases heq : addr = a
    · subst heq; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne heq, Function.update_of_ne heq, h addr hb]

/-- `ConfinedTo M` is closed under monadic bind (`>>=`). -/
theorem bind_prog {α β : Type} {M : ℕ → Prop} {p : Memory.Prog α} {q : α → Memory.Prog β}
    (hp : ConfinedTo M p) (hq : ∀ x, ConfinedTo M (q x)) :
    ConfinedTo M (p >>= q) where
  fr_eq s := by
    rw [StateTransitionSpec.clientState_bind]
    exact ((hq _).fr_eq _).trans (hp.fr_eq s)
  mem_out s addr hnot := by
    rw [StateTransitionSpec.clientState_bind]
    exact ((hq _).mem_out _ addr hnot).trans (hp.mem_out s addr hnot)
  res_eq s₁ s₂ h := by
    rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_bind,
      hp.res_eq s₁ s₂ h]
    exact (hq _).res_eq _ _ (hp.mem_in s₁ s₂ h)
  mem_in s₁ s₂ h addr ha := by
    rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
      hp.res_eq s₁ s₂ h]
    exact (hq _).mem_in _ _ (hp.mem_in s₁ s₂ h) addr ha

/-- `ConfinedTo M` is closed under `if-then-else`. -/
theorem ite_prog {α : Type} {M : ℕ → Prop} {P : Prop} [Decidable P] {p₁ p₂ : Memory.Prog α}
    (h₁ : P → ConfinedTo M p₁) (h₂ : ¬P → ConfinedTo M p₂) :
    ConfinedTo M (if P then p₁ else p₂) := by
  by_cases hP : P
  · rw [ite_eq_left hP]; exact h₁ hP
  · rw [ite_eq_right hP]; exact h₂ hP

/-- `ConfinedTo M` is closed under bounded iteration (`iterate`). -/
theorem iterate_prog {δ σ : Type} {M : ℕ → Prop} {body : δ × σ → Memory.Prog σ}
    (d : δ) (hb : ∀ a, ConfinedTo M (body (d, a))) (fuel : ℕ) (a₀ : σ) :
    ConfinedTo M (iterate body d fuel a₀) := by
  induction fuel generalizing a₀ with
  | zero => exact pure_prog a₀
  | succ k ih =>
    unfold iterate
    exact bind_prog (hb a₀) (fun a₁ => ih a₁)

/-- Lift a read-only program `p` with `clientState s p = s` and `M`-determined `clientResult` into
`ConfinedTo M p`. -/
theorem of_readOnly {α : Type} {M : ℕ → Prop} {p : Memory.Prog α}
    (hst : ∀ s, (Memory.spec 0).clientState s p = s)
    (hres : ∀ s₁ s₂, (∀ addr, M addr → s₁.mem addr = s₂.mem addr) →
      (Memory.spec 0).clientResult s₁ p = (Memory.spec 0).clientResult s₂ p) :
    ConfinedTo M p where
  fr_eq s := by rw [hst]
  mem_out s _ _ := by rw [hst]
  res_eq := hres
  mem_in s₁ s₂ h addr ha := by rw [hst, hst]; exact h addr ha

/-- `readPackedCompGenProg` is confined to `M` whenever `[base + off, base + off + packedWords nMax
k w)` lies inside `M`. -/
theorem readPackedComp_prog {M : ℕ → Prop} {base off k w idx nMax : ℕ}
    (hw : 0 < w) (hidx : idx < nMax)
    (hsub : ∀ addr, base + off ≤ addr → addr < base + off + packedWords nMax k w → M addr) :
    ConfinedTo M (readPackedCompGenProg (((base, off), (k, w)), idx)) := by
  refine of_readOnly
    (fun s => by
      simpa only [StateTransitionSpec.clientState] using
        runClient_state_readPackedCompGenProg (((base, off), (k, w)), idx) s)
    (fun s₁ s₂ h => ?_)
  rw [clientResult_readPackedCompGenProg, clientResult_readPackedCompGenProg]
  exact readPacked_congr hw (fun addr ha => h addr (hsub addr ha.1 ha.2)) hidx

/-- `writePackedCompGenProg` is confined to `M` whenever `[base + off, base + off + packedWords
nMax k w)` lies inside `M`. -/
theorem writePackedComp_prog {M : ℕ → Prop} {base off k w idx val nMax : ℕ}
    (hw : 0 < w) (hidx : idx < nMax)
    (hsub : ∀ addr, base + off ≤ addr → addr < base + off + packedWords nMax k w → M addr) :
    ConfinedTo M (writePackedCompGenProg ((((base, off), (k, w)), idx), val)) where
  fr_eq s := by
    simpa only [StateTransitionSpec.clientState] using
      congrArg Memory.State.frontier
        (runClient_state_writePackedCompGenProg base off k w idx val s)
  mem_out s addr hnot := by
    have hst : ((Memory.spec 0).clientState s
        (writePackedCompGenProg ((((base, off), (k, w)), idx), val))).mem =
        writePacked (base + off) k w s.mem idx val :=
      congrArg Memory.State.mem (clientState_writePackedCompGenProg base off k w idx val s)
    rw [hst]
    exact writePacked_outside hw s.mem hidx val (fun ha => hnot (hsub addr ha.1 ha.2))
  res_eq _ _ _ := rfl
  mem_in s₁ s₂ h addr ha := by
    have hst₁ : ((Memory.spec 0).clientState s₁
        (writePackedCompGenProg ((((base, off), (k, w)), idx), val))).mem =
        writePacked (base + off) k w s₁.mem idx val :=
      congrArg Memory.State.mem (clientState_writePackedCompGenProg base off k w idx val s₁)
    have hst₂ : ((Memory.spec 0).clientState s₂
        (writePackedCompGenProg ((((base, off), (k, w)), idx), val))).mem =
        writePacked (base + off) k w s₂.mem idx val :=
      congrArg Memory.State.mem (clientState_writePackedCompGenProg base off k w idx val s₂)
    rw [hst₁, hst₂]
    have hwOff1 := wordOffset_add_one_lt_packedWords (k := k) hw hidx
    have hm0 : M (base + off + wordOffset k w idx) :=
      hsub _ (Nat.le_add_right _ _) (by omega)
    have hm1 : M (base + off + wordOffset k w idx + 1) :=
      hsub _ (by omega) (by omega)
    have he0 : s₁.mem (base + off + wordOffset k w idx) =
        s₂.mem (base + off + wordOffset k w idx) := h _ hm0
    have he1 : s₁.mem (base + off + wordOffset k w idx + 1) =
        s₂.mem (base + off + wordOffset k w idx + 1) := h _ hm1
    unfold writePacked writeBitSlice
    by_cases h_hi : addr = base + off + wordOffset k w idx + 1
    · subst h_hi
      rw [Function.update_self, Function.update_self,
        Function.update_of_ne (by omega), Function.update_of_ne (by omega), he1]
    · rw [Function.update_of_ne h_hi, Function.update_of_ne h_hi]
      by_cases h_lo : addr = base + off + wordOffset k w idx
      · subst h_lo
        rw [Function.update_self, Function.update_self, he0]
      · rw [Function.update_of_ne h_lo, Function.update_of_ne h_lo, h addr ha]

end ConfinedTo

/-! ## Section 2: Pure Arithmetic and SWAR Helpers -/

private theorem cf_subClampProg (M : ℕ → Prop) (p : ℕ × ℕ) : ConfinedTo M (subClampProg p) := by
  unfold subClampProg
  exact ConfinedTo.ite_prog (fun _ => ConfinedTo.pure_prog _) (fun _ => ConfinedTo.pure_prog _)

private theorem cf_laneGetBoundedProg (M : ℕ → Prop) (d : (ℕ × ℕ) × ℕ) :
    ConfinedTo M (laneGetBoundedProg d) := by
  rcases d with ⟨⟨_, _⟩, _⟩
  unfold laneGetBoundedProg
  exact ConfinedTo.bind_prog (ConfinedTo.pure_prog _) fun _ =>
    ConfinedTo.bind_prog (ConfinedTo.pure_prog _) fun _ => ConfinedTo.pure_prog _

private theorem cf_wordTakeLowBoundedProg (M : ℕ → Prop) (d : (ℕ × ℕ) × ℕ) :
    ConfinedTo M (wordTakeLowBoundedProg d) := by
  rcases d with ⟨⟨_, _⟩, _⟩
  unfold wordTakeLowBoundedProg
  exact ConfinedTo.bind_prog (ConfinedTo.pure_prog _) fun _ =>
    ConfinedTo.bind_prog (ConfinedTo.pure_prog _) fun _ => ConfinedTo.pure_prog _

private theorem cf_wordDropLowBoundedProg (M : ℕ → Prop) (d : (ℕ × ℕ) × ℕ) :
    ConfinedTo M (wordDropLowBoundedProg d) := by
  rcases d with ⟨⟨_, _⟩, _⟩
  unfold wordDropLowBoundedProg
  exact ConfinedTo.bind_prog (ConfinedTo.pure_prog _) fun _ => ConfinedTo.pure_prog _

private theorem cf_wordInsertAtBoundedProg (M : ℕ → Prop) (d : ((ℕ × ℕ) × ℕ) × ℕ) :
    ConfinedTo M (wordInsertAtBoundedProg d) := by
  rcases d with ⟨⟨⟨_, _⟩, _⟩, _⟩
  unfold wordInsertAtBoundedProg
  exact ConfinedTo.bind_prog (cf_wordTakeLowBoundedProg M _) fun _ =>
    ConfinedTo.bind_prog (cf_wordDropLowBoundedProg M _) fun _ =>
    ConfinedTo.bind_prog (ConfinedTo.pure_prog _) fun _ =>
    ConfinedTo.bind_prog (ConfinedTo.pure_prog _) fun _ =>
    ConfinedTo.bind_prog (ConfinedTo.pure_prog _) fun _ => ConfinedTo.pure_prog _

private theorem cf_wordDeleteAtBoundedProg (M : ℕ → Prop) (d : (ℕ × ℕ) × ℕ) :
    ConfinedTo M (wordDeleteAtBoundedProg d) := by
  rcases d with ⟨⟨_, _⟩, _⟩
  unfold wordDeleteAtBoundedProg
  exact ConfinedTo.bind_prog (cf_wordTakeLowBoundedProg M _) fun _ =>
    ConfinedTo.bind_prog (ConfinedTo.pure_prog _) fun _ =>
    ConfinedTo.bind_prog (ConfinedTo.pure_prog _) fun _ =>
    ConfinedTo.bind_prog (ConfinedTo.pure_prog _) fun _ => ConfinedTo.pure_prog _

private theorem cf_wordUpdateAtBoundedProg (M : ℕ → Prop) (d : ((ℕ × ℕ) × ℕ) × ℕ) :
    ConfinedTo M (wordUpdateAtBoundedProg d) := by
  rcases d with ⟨⟨⟨_, _⟩, _⟩, _⟩
  unfold wordUpdateAtBoundedProg
  exact ConfinedTo.bind_prog (cf_wordDeleteAtBoundedProg M _) fun _ =>
    cf_wordInsertAtBoundedProg M _

private theorem cf_swarOnesBoundedProg (M : ℕ → Prop) (d : ℕ × ℕ) :
    ConfinedTo M (swarOnesBoundedProg d) := by
  rcases d with ⟨_, _⟩
  unfold swarOnesBoundedProg
  simp only [pure_bind]
  exact ConfinedTo.pure_prog _

private theorem cf_ltMaskBoundedProg (M : ℕ → Prop) (d : (ℕ × ℕ) × (ℕ × ℕ)) :
    ConfinedTo M (ltMaskBoundedProg d) := by
  rcases d with ⟨⟨_, _⟩, ⟨_, _⟩⟩
  unfold ltMaskBoundedProg
  simp only [pure_bind]
  exact ConfinedTo.bind_prog (cf_swarOnesBoundedProg M _) fun _ =>
    ConfinedTo.bind_prog (cf_subClampProg M _) fun _ => ConfinedTo.pure_prog _

private theorem cf_swarRankInnerProg (M : ℕ → Prop) (d : ((ℕ × ℕ) × ℕ) × (ℕ × ℕ)) :
    ConfinedTo M (swarRankInnerProg d) := by
  rcases d with ⟨⟨⟨_, _⟩, _⟩, ⟨_, _⟩⟩
  unfold swarRankInnerProg
  simp only [pure_bind]
  refine ConfinedTo.bind_prog (cf_ltMaskBoundedProg M _) fun _ =>
    ConfinedTo.bind_prog (cf_swarOnesBoundedProg M _) fun _ =>
    ConfinedTo.bind_prog (cf_laneGetBoundedProg M _) fun _ => ?_
  exact ConfinedTo.ite_prog (fun _ => ConfinedTo.pure_prog _) (fun _ => ConfinedTo.pure_prog _)

private theorem cf_swarRankClampedProg (M : ℕ → Prop) (d : ((ℕ × ℕ) × ℕ) × (ℕ × ℕ)) :
    ConfinedTo M (swarRankClampedProg d) := by
  rcases d with ⟨⟨⟨_, _⟩, _⟩, ⟨_, _⟩⟩
  unfold swarRankClampedProg
  simp only [pure_bind]
  exact ConfinedTo.ite_prog (fun _ => cf_swarRankInnerProg M _) (fun _ => cf_swarRankInnerProg M _)

private theorem cf_splitFullLeafProg (M : ℕ → Prop)
    (d : (SplitParams × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) :
    ConfinedTo M (splitFullLeafProg d) := by
  rcases d with ⟨⟨⟨⟨_, _⟩, _⟩, _⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩
  unfold splitFullLeafProg
  exact ConfinedTo.bind_prog (cf_wordTakeLowBoundedProg M _) fun _ =>
    ConfinedTo.bind_prog (cf_wordTakeLowBoundedProg M _) fun _ => ConfinedTo.pure_prog _

private theorem cf_splitFullBranchProg (M : ℕ → Prop)
    (d : (SplitParams × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) :
    ConfinedTo M (splitFullBranchProg d) := by
  rcases d with ⟨⟨⟨⟨_, _⟩, _⟩, _⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩
  unfold splitFullBranchProg
  exact ConfinedTo.bind_prog (cf_wordTakeLowBoundedProg M _) fun _ =>
    ConfinedTo.bind_prog (cf_wordTakeLowBoundedProg M _) fun _ => ConfinedTo.pure_prog _

private theorem cf_splitFullNodeAtProg (M : ℕ → Prop)
    (d : SplitParams × (ℕ × (ℕ × ℕ))) :
    ConfinedTo M (splitFullNodeAtProg d) := by
  rcases d with ⟨⟨⟨_, _⟩, _⟩, ⟨_, ⟨_, _⟩⟩⟩
  unfold splitFullNodeAtProg
  simp only [pure_bind]
  refine ConfinedTo.bind_prog (cf_laneGetBoundedProg M _) fun _ =>
    ConfinedTo.bind_prog (cf_wordDropLowBoundedProg M _) fun _ =>
    ConfinedTo.bind_prog (cf_wordDropLowBoundedProg M _) fun _ => ?_
  exact ConfinedTo.ite_prog (fun _ => cf_splitFullLeafProg M _)
    (fun _ => cf_splitFullBranchProg M _)

private theorem cf_computeRootSplitProg (M : ℕ → Prop)
    (d : (SplitParams × ℕ) × (ℕ × (ℕ × ℕ))) :
    ConfinedTo M (computeRootSplitProg d) := by
  rcases d with ⟨⟨_, _⟩, _⟩
  unfold computeRootSplitProg
  simp only [pure_bind]
  exact ConfinedTo.bind_prog (cf_splitFullNodeAtProg M _) fun _ => ConfinedTo.pure_prog _

private theorem cf_computeChildSplitProg (M : ℕ → Prop)
    (d : ((SplitParams × (ℕ × ℕ)) × ℕ) × ((ℕ × (ℕ × ℕ)) × (ℕ × (ℕ × ℕ)))) :
    ConfinedTo M (computeChildSplitProg d) := by
  rcases d with ⟨⟨⟨_, ⟨_, _⟩⟩, _⟩, ⟨_, _⟩⟩
  unfold computeChildSplitProg
  simp only [pure_bind]
  exact ConfinedTo.bind_prog (cf_splitFullNodeAtProg M _) fun _ =>
    ConfinedTo.bind_prog (cf_wordInsertAtBoundedProg M _) fun _ =>
    ConfinedTo.bind_prog (cf_wordInsertAtBoundedProg M _) fun _ => ConfinedTo.pure_prog _

private theorem cf_leafInsertShiftProg (M : ℕ → Prop)
    (d : (SplitParams × (ℕ × ℕ)) × ((ℕ × ℕ) × (ℕ × (ℕ × ℕ)))) :
    ConfinedTo M (leafInsertShiftProg d) := by
  rcases d with ⟨⟨⟨⟨_, _⟩, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, ⟨_, _⟩⟩⟩⟩
  unfold leafInsertShiftProg
  exact ConfinedTo.bind_prog (cf_wordInsertAtBoundedProg M _) fun _ =>
    ConfinedTo.bind_prog (cf_wordInsertAtBoundedProg M _) fun _ => ConfinedTo.pure_prog _

private theorem cf_leafInsertHitOrShiftProg (M : ℕ → Prop)
    (d : (SplitParams × (ℕ × ℕ)) × (((ℕ × ℕ) × ℕ) × (ℕ × (ℕ × ℕ)))) :
    ConfinedTo M (leafInsertHitOrShiftProg d) := by
  rcases d with ⟨⟨_, _⟩, ⟨⟨⟨_, _⟩, _⟩, _⟩⟩
  unfold leafInsertHitOrShiftProg
  exact ConfinedTo.ite_prog
    (fun _ => ConfinedTo.bind_prog (cf_wordUpdateAtBoundedProg M _) fun _ =>
      ConfinedTo.pure_prog _)
    (fun _ => cf_leafInsertShiftProg M _)

private theorem cf_computeLeafInsertNodeProg (M : ℕ → Prop)
    (d : (SplitParams × (ℕ × ℕ)) × (ℕ × (ℕ × ℕ))) :
    ConfinedTo M (computeLeafInsertNodeProg d) := by
  rcases d with ⟨⟨⟨⟨_, _⟩, _⟩, ⟨_, _⟩⟩, _⟩
  unfold computeLeafInsertNodeProg
  simp only [pure_bind]
  refine ConfinedTo.bind_prog (cf_swarRankClampedProg M _) fun _ =>
    ConfinedTo.bind_prog (cf_laneGetBoundedProg M _) fun _ => ?_
  exact ConfinedTo.ite_prog
    (fun _ => cf_leafInsertHitOrShiftProg M _)
    (fun _ => cf_leafInsertShiftProg M _)

private theorem cf_descendBranchNextProg (M : ℕ → Prop)
    (d : (BTreeSliceCtx × ℕ) × (ℕ × (ℕ × ℕ))) :
    ConfinedTo M (descendBranchNextProg d) := by
  rcases d with ⟨⟨_, _⟩, _⟩
  unfold descendBranchNextProg
  simp only [pure_bind]
  exact ConfinedTo.bind_prog (cf_swarRankClampedProg M _) fun _ => cf_laneGetBoundedProg M _

private theorem cf_btreeLookupHitProg (M : ℕ → Prop)
    (d : (BTreeSliceCtx × ℕ) × ((ℕ × ℕ) × (ℕ × (ℕ × ℕ)))) :
    ConfinedTo M (btreeLookupHitProg d) := by
  rcases d with ⟨⟨_, _⟩, ⟨⟨_, _⟩, _⟩⟩
  unfold btreeLookupHitProg
  exact ConfinedTo.ite_prog
    (fun _ => ConfinedTo.bind_prog (cf_laneGetBoundedProg M _) fun _ => ConfinedTo.pure_prog _)
    (fun _ => ConfinedTo.pure_prog _)

private theorem cf_btreeLookupRankProg (M : ℕ → Prop)
    (d : (BTreeSliceCtx × ℕ) × (ℕ × (ℕ × ℕ))) :
    ConfinedTo M (btreeLookupRankProg d) := by
  rcases d with ⟨⟨_, _⟩, _⟩
  unfold btreeLookupRankProg
  simp only [pure_bind]
  refine ConfinedTo.bind_prog (cf_swarRankClampedProg M _) fun _ =>
    ConfinedTo.bind_prog (cf_laneGetBoundedProg M _) fun _ => ?_
  exact ConfinedTo.ite_prog (fun _ => cf_btreeLookupHitProg M _) (fun _ => ConfinedTo.pure_prog _)

/-! ## Section 3: `LargeBTreeProg` Confinement -/

private def SliceHdrConf (M : ℕ → Prop) : SliceHdrCtx → Prop
  | (((mb, ob), (pb, wv)), hdrBase) =>
    ∃ cap, 0 < wv ∧ hdrBase + 1 < cap ∧
      (∀ addr, mb + ob ≤ addr → addr < mb + ob + packedWords cap pb wv → M addr)

private def SliceNodeConf (M : ℕ → Prop) : SliceNodeCtx → Prop
  | ((((mb, om), (ok, ov)), ((wv, wm), (wk, wvl))), (ns, nodeBase)) =>
    ∃ tot, 0 < wv ∧ 1 ≤ ns ∧ nodeBase + ns ≤ tot ∧
      (∀ addr, mb + om ≤ addr → addr < mb + om + packedWords tot wm wv → M addr) ∧
      (∀ addr, mb + ok ≤ addr → addr < mb + ok + packedWords tot wk wv → M addr) ∧
      (∀ addr, mb + ov ≤ addr → addr < mb + ov + packedWords tot wvl wv → M addr)

/-- Bundle certifying that `ctx : BTreeSliceCtx` belongs to a valid `BTreeEpochLayout` whose owned
addresses lie inside `M`. -/
@[expose] def BTreeSliceConf (M : ℕ → Prop) (ctx : BTreeSliceCtx) : Prop :=
  match unpackSliceCtx ctx with
  | (L, (b, role)) =>
    0 < L.w ∧ 1 ≤ L.nSlice ∧ b < L.numBuckets ∧ role < 3 ∧
      (∀ addr, L.OwnsAddr addr → M addr)

private theorem sliceHdrConf_of_btreeSliceConf {M : ℕ → Prop} {ctx : BTreeSliceCtx}
    (h : BTreeSliceConf M ctx) :
    SliceHdrConf M (ctxHdrAt ctx (16 * ctxB ctx + 6 + 2 * ctxRole ctx)) := by
  rcases ctx with ⟨⟨⟨⟨mb, ob⟩, ⟨om, ⟨ok, ov⟩⟩⟩, ⟨⟨pb, wv⟩, ⟨wm, ⟨wk, wvl⟩⟩⟩⟩,
    ⟨⟨⟨fp, wvL⟩, ⟨tm, ns⟩⟩, ⟨nb, ⟨b, role⟩⟩⟩⟩
  dsimp only [BTreeSliceConf, unpackSliceCtx, BTreeEpochLayout.OwnsAddr, ctxHdrAt,
    ctxMbOb, ctxPbWv, ctxB, ctxRole] at h ⊢
  obtain ⟨hw, _, hb, hrole, hM⟩ := h
  exact ⟨16 * nb, hw, by omega, fun addr h1 h2 => hM addr (Or.inl ⟨h1, h2⟩)⟩

private theorem sliceNodeConf_of_btreeSliceConf {M : ℕ → Prop} {ctx : BTreeSliceCtx}
    (h : BTreeSliceConf M ctx) :
    SliceNodeConf M (ctxNodeAt ctx ((3 * ctxB ctx + ctxRole ctx) * ctxNs ctx)) := by
  rcases ctx with ⟨⟨⟨⟨mb, ob⟩, ⟨om, ⟨ok, ov⟩⟩⟩, ⟨⟨pb, wv⟩, ⟨wm, ⟨wk, wvl⟩⟩⟩⟩,
    ⟨⟨⟨fp, wvL⟩, ⟨tm, ns⟩⟩, ⟨nb, ⟨b, role⟩⟩⟩⟩
  dsimp only [BTreeSliceConf, unpackSliceCtx, BTreeEpochLayout.OwnsAddr,
    BTreeEpochLayout.totalNodes, ctxNodeAt, ctxMb, ctxOm, ctxOkOv, ctxWv, ctxWm, ctxWkWvl,
    ctxNs, ctxB, ctxRole] at h ⊢
  obtain ⟨hw, hns1, hb, hrole, hM⟩ := h
  have hbr : 3 * b + role + 1 ≤ 3 * nb := by omega
  have htot : (3 * b + role) * ns + ns ≤ 3 * nb * ns := by
    calc (3 * b + role) * ns + ns = (3 * b + role + 1) * ns := by ring
      _ ≤ 3 * nb * ns := Nat.mul_le_mul_right _ hbr
  refine ⟨3 * nb * ns, hw, hns1, htot,
    fun addr h1 h2 => hM addr (Or.inr (Or.inl ⟨h1, h2⟩)),
    fun addr h1 h2 => hM addr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))),
    fun addr h1 h2 => hM addr (Or.inr (Or.inr (Or.inr ⟨h1, h2⟩)))⟩

private theorem cf_readSliceNodeAtProg {M : ℕ → Prop} {nctx : SliceNodeCtx} {u : ℕ}
    (h : SliceNodeConf M nctx) :
    ConfinedTo M (readSliceNodeAtProg (nctx, u)) := by
  rcases nctx with ⟨⟨⟨⟨mb, om⟩, ⟨ok, ov⟩⟩, ⟨⟨wv, wm⟩, ⟨wk, wvl⟩⟩⟩, ⟨ns, nodeBase⟩⟩
  obtain ⟨tot, hw, hns1, hnb, hm1, hm2, hm3⟩ := h
  unfold readSliceNodeAtProg
  refine ConfinedTo.ite_prog (fun hu => ?_) (fun _ => ?_)
  · simp only [pure_bind]
    exact ConfinedTo.bind_prog (ConfinedTo.readPackedComp_prog hw (by omega) hm1) fun _ =>
      ConfinedTo.bind_prog (ConfinedTo.readPackedComp_prog hw (by omega) hm2) fun _ =>
      ConfinedTo.bind_prog (ConfinedTo.readPackedComp_prog hw (by omega) hm3) fun _ =>
      ConfinedTo.pure_prog _
  · exact ConfinedTo.bind_prog (ConfinedTo.readPackedComp_prog hw (by omega) hm1) fun _ =>
      ConfinedTo.pure_prog _

private theorem cf_writeSliceNodeAtProg {M : ℕ → Prop} {nctx : SliceNodeCtx} {u : ℕ}
    {nd : ℕ × (ℕ × ℕ)} (h : SliceNodeConf M nctx) :
    ConfinedTo M (writeSliceNodeAtProg ((nctx, u), nd)) := by
  rcases nctx with ⟨⟨⟨⟨mb, om⟩, ⟨ok, ov⟩⟩, ⟨⟨wv, wm⟩, ⟨wk, wvl⟩⟩⟩, ⟨ns, nodeBase⟩⟩
  rcases nd with ⟨mw, ⟨kw, vw⟩⟩
  obtain ⟨tot, hw, _, hnb, hm1, hm2, hm3⟩ := h
  unfold writeSliceNodeAtProg
  refine ConfinedTo.ite_prog (fun hu => ?_) (fun _ => ConfinedTo.pure_prog _)
  simp only [pure_bind]
  exact ConfinedTo.bind_prog (ConfinedTo.writePackedComp_prog hw (by omega) hm1) fun _ =>
    ConfinedTo.bind_prog (ConfinedTo.writePackedComp_prog hw (by omega) hm2) fun _ =>
    ConfinedTo.writePackedComp_prog hw (by omega) hm3

private theorem cf_writeTwoNodesAtProg {M : ℕ → Prop} {nctx : SliceNodeCtx}
    {pair : (ℕ × (ℕ × (ℕ × ℕ))) × (ℕ × (ℕ × (ℕ × ℕ)))} (h : SliceNodeConf M nctx) :
    ConfinedTo M (writeTwoNodesAtProg (nctx, pair)) := by
  rcases pair with ⟨⟨_, _⟩, ⟨_, _⟩⟩
  unfold writeTwoNodesAtProg
  exact ConfinedTo.bind_prog (cf_writeSliceNodeAtProg h) fun _ => cf_writeSliceNodeAtProg h

private theorem cf_readSliceHdrAtProg {M : ℕ → Prop} {hctx : SliceHdrCtx}
    (h : SliceHdrConf M hctx) :
    ConfinedTo M (readSliceHdrAtProg hctx) := by
  rcases hctx with ⟨⟨⟨mb, ob⟩, ⟨pb, wv⟩⟩, hdrBase⟩
  obtain ⟨cap, hw, hsl, hm⟩ := h
  unfold readSliceHdrAtProg
  exact ConfinedTo.bind_prog (ConfinedTo.readPackedComp_prog hw (by omega) hm) fun _ =>
    ConfinedTo.bind_prog (ConfinedTo.readPackedComp_prog hw hsl hm) fun _ =>
    ConfinedTo.pure_prog _

private theorem cf_writeSliceHdrAtProg {M : ℕ → Prop} {hctx : SliceHdrCtx} {isRoot val : ℕ}
    (h : SliceHdrConf M hctx) :
    ConfinedTo M (writeSliceHdrAtProg (hctx, (isRoot, val))) := by
  rcases hctx with ⟨⟨⟨mb, ob⟩, ⟨pb, wv⟩⟩, hdrBase⟩
  obtain ⟨cap, hw, hsl, hm⟩ := h
  unfold writeSliceHdrAtProg
  refine ConfinedTo.ite_prog (fun hi => ?_) (fun _ => ConfinedTo.pure_prog _)
  simp only [pure_bind]
  exact ConfinedTo.writePackedComp_prog hw (by omega) hm

private theorem cf_descendStepProg {M : ℕ → Prop} {ctx : BTreeSliceCtx} {q cur : ℕ}
    (h : BTreeSliceConf M ctx) :
    ConfinedTo M (descendStepProg ((ctx, q), cur)) := by
  have hnode := sliceNodeConf_of_btreeSliceConf h
  unfold descendStepProg
  simp only [pure_bind]
  refine ConfinedTo.bind_prog (cf_readSliceNodeAtProg hnode) fun _ => ?_
  exact ConfinedTo.ite_prog (fun _ => ConfinedTo.pure_prog _)
    (fun _ => cf_descendBranchNextProg M _)

private theorem cf_descendLoopProg {M : ℕ → Prop} {ctx : BTreeSliceCtx} {q cur fuel : ℕ}
    (h : BTreeSliceConf M ctx) :
    ConfinedTo M (descendLoopProg (((ctx, q), cur), fuel)) := by
  unfold descendLoopProg
  exact ConfinedTo.iterate_prog (ctx, q) (fun _ => cf_descendStepProg h) fuel cur

private theorem cf_btreeLookupLeafProg {M : ℕ → Prop} {ctx : BTreeSliceCtx} {leafIdx q : ℕ}
    (h : BTreeSliceConf M ctx) :
    ConfinedTo M (btreeLookupLeafProg (ctx, (leafIdx, q))) := by
  have hnode := sliceNodeConf_of_btreeSliceConf h
  unfold btreeLookupLeafProg
  simp only [pure_bind]
  exact ConfinedTo.bind_prog (cf_readSliceNodeAtProg hnode) fun _ => cf_btreeLookupRankProg M _

private theorem cf_btreeLookupNonEmptyProg {M : ℕ → Prop} {ctx : BTreeSliceCtx}
    {q rt fuel : ℕ} (h : BTreeSliceConf M ctx) :
    ConfinedTo M (btreeLookupNonEmptyProg (((ctx, q), rt), fuel)) := by
  unfold btreeLookupNonEmptyProg
  exact ConfinedTo.bind_prog (cf_descendLoopProg h) fun _ => cf_btreeLookupLeafProg h

/-- `btreeLookupBoundedProg` is confined to `M` under `BTreeSliceConf M ctx`. -/
theorem confinedTo_btreeLookupBoundedProg {M : ℕ → Prop} {ctx : BTreeSliceCtx} {q : ℕ}
    (h : BTreeSliceConf M ctx) :
    ConfinedTo M (btreeLookupBoundedProg (ctx, q)) := by
  have hhdr := sliceHdrConf_of_btreeSliceConf h
  unfold btreeLookupBoundedProg
  simp only [pure_bind]
  refine ConfinedTo.bind_prog (cf_readSliceHdrAtProg hhdr) fun _ => ?_
  exact ConfinedTo.ite_prog (fun _ => ConfinedTo.pure_prog _)
    (fun _ => cf_btreeLookupNonEmptyProg h)

private theorem cf_btreeDeleteHitProg {M : ℕ → Prop} {ctx : BTreeSliceCtx}
    {q nodeBase leafIdx cnt r kAt : ℕ} {nd : ℕ × (ℕ × ℕ)}
    (hnode : SliceNodeConf M (ctxNodeAt ctx nodeBase)) :
    ConfinedTo M
      (btreeDeleteHitProg (((ctx, q), (nodeBase, leafIdx)), ((cnt, r), (kAt, nd)))) := by
  unfold btreeDeleteHitProg
  refine ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ConfinedTo.pure_prog _)
  simp only [pure_bind]
  exact ConfinedTo.bind_prog (cf_wordDeleteAtBoundedProg M _) fun _ =>
    ConfinedTo.bind_prog (cf_wordDeleteAtBoundedProg M _) fun _ =>
    cf_writeSliceNodeAtProg hnode

private theorem cf_btreeDeleteRankProg {M : ℕ → Prop} {ctx : BTreeSliceCtx}
    {q nodeBase leafIdx : ℕ} {nd : ℕ × (ℕ × ℕ)}
    (hnode : SliceNodeConf M (ctxNodeAt ctx nodeBase)) :
    ConfinedTo M (btreeDeleteRankProg (((ctx, q), (nodeBase, leafIdx)), nd)) := by
  unfold btreeDeleteRankProg
  simp only [pure_bind]
  refine ConfinedTo.bind_prog (cf_swarRankClampedProg M _) fun _ =>
    ConfinedTo.bind_prog (cf_laneGetBoundedProg M _) fun _ => ?_
  exact ConfinedTo.ite_prog (fun _ => cf_btreeDeleteHitProg hnode)
    (fun _ => ConfinedTo.pure_prog _)

private theorem cf_btreeDeleteLeafProg {M : ℕ → Prop} {ctx : BTreeSliceCtx} {leafIdx q : ℕ}
    (h : BTreeSliceConf M ctx) :
    ConfinedTo M (btreeDeleteLeafProg (ctx, (leafIdx, q))) := by
  have hnode := sliceNodeConf_of_btreeSliceConf h
  unfold btreeDeleteLeafProg
  simp only [pure_bind]
  exact ConfinedTo.bind_prog (cf_readSliceNodeAtProg hnode) fun _ => cf_btreeDeleteRankProg hnode

private theorem cf_btreeDeleteNonEmptyProg {M : ℕ → Prop} {ctx : BTreeSliceCtx}
    {q rt fuel : ℕ} (h : BTreeSliceConf M ctx) :
    ConfinedTo M (btreeDeleteNonEmptyProg (((ctx, q), rt), fuel)) := by
  unfold btreeDeleteNonEmptyProg
  exact ConfinedTo.bind_prog (cf_descendLoopProg h) fun _ => cf_btreeDeleteLeafProg h

/-- `btreeDeleteBoundedProg` is confined to `M` under `BTreeSliceConf M ctx`. -/
theorem confinedTo_btreeDeleteBoundedProg {M : ℕ → Prop} {ctx : BTreeSliceCtx} {q : ℕ}
    (h : BTreeSliceConf M ctx) :
    ConfinedTo M (btreeDeleteBoundedProg (ctx, q)) := by
  have hhdr := sliceHdrConf_of_btreeSliceConf h
  unfold btreeDeleteBoundedProg
  simp only [pure_bind]
  refine ConfinedTo.bind_prog (cf_readSliceHdrAtProg hhdr) fun _ => ?_
  exact ConfinedTo.ite_prog (fun _ => ConfinedTo.pure_prog _)
    (fun _ => cf_btreeDeleteNonEmptyProg h)

private theorem cf_btreeUpdateHitProg {M : ℕ → Prop} {ctx : BTreeSliceCtx}
    {q newVal nodeBase leafIdx r kAt : ℕ} {nd : ℕ × (ℕ × ℕ)}
    (hnode : SliceNodeConf M (ctxNodeAt ctx nodeBase)) :
    ConfinedTo M
      (btreeUpdateHitProg (((ctx, (q, newVal)), (nodeBase, leafIdx)), ((r, kAt), nd))) := by
  unfold btreeUpdateHitProg
  refine ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ConfinedTo.pure_prog _)
  exact ConfinedTo.bind_prog (cf_wordUpdateAtBoundedProg M _) fun _ =>
    cf_writeSliceNodeAtProg hnode

private theorem cf_btreeUpdateRankProg {M : ℕ → Prop} {ctx : BTreeSliceCtx}
    {q newVal nodeBase leafIdx : ℕ} {nd : ℕ × (ℕ × ℕ)}
    (hnode : SliceNodeConf M (ctxNodeAt ctx nodeBase)) :
    ConfinedTo M (btreeUpdateRankProg (((ctx, (q, newVal)), (nodeBase, leafIdx)), nd)) := by
  unfold btreeUpdateRankProg
  simp only [pure_bind]
  refine ConfinedTo.bind_prog (cf_swarRankClampedProg M _) fun _ =>
    ConfinedTo.bind_prog (cf_laneGetBoundedProg M _) fun _ => ?_
  exact ConfinedTo.ite_prog (fun _ => cf_btreeUpdateHitProg hnode)
    (fun _ => ConfinedTo.pure_prog _)

private theorem cf_btreeUpdateLeafProg {M : ℕ → Prop} {ctx : BTreeSliceCtx}
    {leafIdx q newVal : ℕ} (h : BTreeSliceConf M ctx) :
    ConfinedTo M (btreeUpdateLeafProg (ctx, (leafIdx, (q, newVal)))) := by
  have hnode := sliceNodeConf_of_btreeSliceConf h
  unfold btreeUpdateLeafProg
  simp only [pure_bind]
  exact ConfinedTo.bind_prog (cf_readSliceNodeAtProg hnode) fun _ => cf_btreeUpdateRankProg hnode

private theorem cf_btreeUpdateNonEmptyProg {M : ℕ → Prop} {ctx : BTreeSliceCtx}
    {q newVal rt : ℕ} (h : BTreeSliceConf M ctx) :
    ConfinedTo M (btreeUpdateNonEmptyProg ((ctx, (q, newVal)), rt)) := by
  unfold btreeUpdateNonEmptyProg
  exact ConfinedTo.bind_prog (cf_descendLoopProg h) fun _ => cf_btreeUpdateLeafProg h

/-- `btreeUpdateBoundedProg` is confined to `M` under `BTreeSliceConf M ctx`. -/
theorem confinedTo_btreeUpdateBoundedProg {M : ℕ → Prop} {ctx : BTreeSliceCtx} {q newVal : ℕ}
    (h : BTreeSliceConf M ctx) :
    ConfinedTo M (btreeUpdateBoundedProg (ctx, (q, newVal))) := by
  have hhdr := sliceHdrConf_of_btreeSliceConf h
  unfold btreeUpdateBoundedProg
  simp only [pure_bind]
  refine ConfinedTo.bind_prog (cf_readSliceHdrAtProg hhdr) fun _ => ?_
  exact ConfinedTo.ite_prog (fun _ => ConfinedTo.pure_prog _)
    (fun _ => cf_btreeUpdateNonEmptyProg h)

private theorem cf_initEmptyRootAtProg {M : ℕ → Prop} {nctx : SliceNodeCtx} {hctx : SliceHdrCtx}
    (hnode : SliceNodeConf M nctx) (hhdr : SliceHdrConf M hctx) :
    ConfinedTo M (initEmptyRootAtProg (nctx, hctx)) := by
  unfold initEmptyRootAtProg
  exact ConfinedTo.bind_prog (cf_writeSliceNodeAtProg hnode) fun _ =>
    ConfinedTo.bind_prog (cf_writeSliceHdrAtProg hhdr) fun _ =>
    ConfinedTo.bind_prog (cf_writeSliceHdrAtProg hhdr) fun _ => ConfinedTo.pure_prog _

private theorem cf_execRootSplitProg {M : ℕ → Prop} {ctx : BTreeSliceCtx}
    {hdrBase nodeBase al rt : ℕ} {rootNd : ℕ × (ℕ × ℕ)}
    (hnode : SliceNodeConf M (ctxNodeAt ctx nodeBase))
    (hhdr : SliceHdrConf M (ctxHdrAt ctx hdrBase)) :
    ConfinedTo M (execRootSplitProg ((ctx, (hdrBase, nodeBase)), ((al, rt), rootNd))) := by
  unfold execRootSplitProg
  refine ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ConfinedTo.pure_prog _)
  exact ConfinedTo.bind_prog (cf_computeRootSplitProg M _) fun _ =>
    ConfinedTo.bind_prog (cf_writeTwoNodesAtProg hnode) fun _ =>
    ConfinedTo.bind_prog (cf_writeSliceNodeAtProg hnode) fun _ =>
    ConfinedTo.bind_prog (cf_writeSliceHdrAtProg hhdr) fun _ => ConfinedTo.pure_prog _

private theorem cf_prepareNonEmptyRootProg {M : ℕ → Prop} {ctx : BTreeSliceCtx}
    {hdrBase nodeBase : ℕ} {hdr : ℕ × ℕ}
    (hnode : SliceNodeConf M (ctxNodeAt ctx nodeBase))
    (hhdr : SliceHdrConf M (ctxHdrAt ctx hdrBase)) :
    ConfinedTo M (prepareNonEmptyRootProg ((ctx, (hdrBase, nodeBase)), hdr)) := by
  unfold prepareNonEmptyRootProg
  simp only [pure_bind]
  refine ConfinedTo.bind_prog (cf_readSliceNodeAtProg hnode) fun _ => ?_
  exact ConfinedTo.ite_prog (fun _ => cf_execRootSplitProg hnode hhdr)
    (fun _ => ConfinedTo.pure_prog _)

private theorem cf_prepareRootBoundedProg {M : ℕ → Prop} {ctx : BTreeSliceCtx}
    (h : BTreeSliceConf M ctx) :
    ConfinedTo M (prepareRootBoundedProg ctx) := by
  have hhdr := sliceHdrConf_of_btreeSliceConf h
  have hnode := sliceNodeConf_of_btreeSliceConf h
  unfold prepareRootBoundedProg
  simp only [pure_bind]
  refine ConfinedTo.bind_prog (cf_readSliceHdrAtProg hhdr) fun _ => ?_
  exact ConfinedTo.ite_prog
    (fun _ => cf_initEmptyRootAtProg hnode hhdr)
    (fun _ => cf_prepareNonEmptyRootProg hnode hhdr)

private theorem cf_finishChildSplitWritesProg {M : ℕ → Prop} {ctx : BTreeSliceCtx}
    {q hdrBase nodeBase al cur childIdx : ℕ}
    {res : ((ℕ × (ℕ × ℕ)) × (ℕ × (ℕ × ℕ))) × ((ℕ × (ℕ × ℕ)) × ℕ)}
    (hnode : SliceNodeConf M (ctxNodeAt ctx nodeBase))
    (hhdr : SliceHdrConf M (ctxHdrAt ctx hdrBase)) :
    ConfinedTo M (finishChildSplitWritesProg
      (((ctx, q), (hdrBase, nodeBase)), ((al, (cur, childIdx)), res))) := by
  unfold finishChildSplitWritesProg
  refine ConfinedTo.bind_prog (cf_writeTwoNodesAtProg hnode) fun _ =>
    ConfinedTo.bind_prog (cf_writeSliceNodeAtProg hnode) fun _ =>
    ConfinedTo.bind_prog (cf_writeSliceHdrAtProg hhdr) fun _ => ?_
  exact ConfinedTo.ite_prog (fun _ => ConfinedTo.pure_prog _) (fun _ => ConfinedTo.pure_prog _)

private theorem cf_splitChildBodyProg {M : ℕ → Prop} {ctx : BTreeSliceCtx}
    {q hdrBase al cur r childIdx : ℕ} (h : BTreeSliceConf M ctx)
    (hhdr : SliceHdrConf M (ctxHdrAt ctx hdrBase)) :
    ConfinedTo M (splitChildBodyProg (((ctx, q), (hdrBase, al)), (cur, (r, childIdx)))) := by
  have hnode := sliceNodeConf_of_btreeSliceConf h
  unfold splitChildBodyProg
  simp only [pure_bind]
  exact ConfinedTo.bind_prog (cf_readSliceNodeAtProg hnode) fun _ =>
    ConfinedTo.bind_prog (cf_readSliceNodeAtProg hnode) fun _ =>
    ConfinedTo.bind_prog (cf_computeChildSplitProg M _) fun _ =>
    cf_finishChildSplitWritesProg hnode hhdr

private theorem cf_splitChildAndStepProg {M : ℕ → Prop} {ctx : BTreeSliceCtx}
    {q cur r childIdx : ℕ} (h : BTreeSliceConf M ctx) :
    ConfinedTo M (splitChildAndStepProg ((ctx, q), (cur, (r, childIdx)))) := by
  have hhdr := sliceHdrConf_of_btreeSliceConf h
  unfold splitChildAndStepProg
  simp only [pure_bind]
  refine ConfinedTo.bind_prog (cf_readSliceHdrAtProg hhdr) fun _ => ?_
  exact ConfinedTo.ite_prog (fun _ => cf_splitChildBodyProg h hhdr)
    (fun _ => ConfinedTo.pure_prog _)

private theorem cf_descendSplitBranchProg {M : ℕ → Prop} {ctx : BTreeSliceCtx}
    {q nodeBase cur : ℕ} {nd : ℕ × (ℕ × ℕ)} (h : BTreeSliceConf M ctx)
    (hnode : SliceNodeConf M (ctxNodeAt ctx nodeBase)) :
    ConfinedTo M (descendSplitBranchProg (((ctx, q), (nodeBase, cur)), nd)) := by
  unfold descendSplitBranchProg
  simp only [pure_bind]
  refine ConfinedTo.bind_prog (cf_swarRankClampedProg M _) fun _ =>
    ConfinedTo.bind_prog (cf_laneGetBoundedProg M _) fun _ =>
    ConfinedTo.bind_prog (cf_readSliceNodeAtProg hnode) fun _ => ?_
  exact ConfinedTo.ite_prog (fun _ => cf_splitChildAndStepProg h)
    (fun _ => ConfinedTo.pure_prog _)

private theorem cf_descendSplitStepProg {M : ℕ → Prop} {ctx : BTreeSliceCtx} {q cur : ℕ}
    (h : BTreeSliceConf M ctx) :
    ConfinedTo M (descendSplitStepProg ((ctx, q), cur)) := by
  have hnode := sliceNodeConf_of_btreeSliceConf h
  unfold descendSplitStepProg
  simp only [pure_bind]
  refine ConfinedTo.bind_prog (cf_readSliceNodeAtProg hnode) fun _ => ?_
  exact ConfinedTo.ite_prog (fun _ => ConfinedTo.pure_prog _)
    (fun _ => cf_descendSplitBranchProg h hnode)

private theorem cf_descendSplitLoopProg {M : ℕ → Prop} {ctx : BTreeSliceCtx} {q cur fuel : ℕ}
    (h : BTreeSliceConf M ctx) :
    ConfinedTo M (descendSplitLoopProg (((ctx, q), cur), fuel)) := by
  unfold descendSplitLoopProg
  exact ConfinedTo.iterate_prog (ctx, q) (fun _ => cf_descendSplitStepProg h) fuel cur

private theorem cf_finishLeafInsertBoundedProg {M : ℕ → Prop} {ctx : BTreeSliceCtx}
    {leafIdx q val : ℕ} (h : BTreeSliceConf M ctx) :
    ConfinedTo M (finishLeafInsertBoundedProg (ctx, (leafIdx, (q, val)))) := by
  have hnode := sliceNodeConf_of_btreeSliceConf h
  unfold finishLeafInsertBoundedProg
  simp only [pure_bind]
  exact ConfinedTo.bind_prog (cf_readSliceNodeAtProg hnode) fun _ =>
    ConfinedTo.bind_prog (cf_computeLeafInsertNodeProg M _) fun _ =>
    cf_writeSliceNodeAtProg hnode

/-- `btreeInsertBoundedProg` is confined to `M` under `BTreeSliceConf M ctx`. -/
theorem confinedTo_btreeInsertBoundedProg {M : ℕ → Prop} {ctx : BTreeSliceCtx} {q val : ℕ}
    (h : BTreeSliceConf M ctx) :
    ConfinedTo M (btreeInsertBoundedProg (ctx, (q, val))) := by
  unfold btreeInsertBoundedProg
  exact ConfinedTo.bind_prog (cf_prepareRootBoundedProg h) fun _ =>
    ConfinedTo.bind_prog (cf_descendSplitLoopProg h) fun _ =>
    cf_finishLeafInsertBoundedProg h

/-! ## Section 4: `LargeTrieProg` Confinement -/

/-- Bundle certifying that `ctx : TrieCtx` belongs to a valid `TrieLayout` whose owned addresses
lie inside `M`. -/
@[expose] def TrieConf (M : ℕ → Prop) (ctx : TrieCtx) : Prop :=
  let L := TrieLayout.ofCtx ctx
  0 < L.w ∧ 1 ≤ L.maxNodes ∧ (∀ addr, L.OwnsAddr addr → M addr)

private theorem and_shiftLeft_mask_lt' (x bc : ℕ) :
    x &&& ((1 <<< bc) - 1) < 2 ^ bc := by
  rw [Nat.shiftLeft_eq, one_mul, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (Nat.two_pow_pos bc)

private theorem cf_bufWalkStepProg {M : ℕ → Prop} {ctx : TrieCtx} {st : (ℕ × ℕ) × ℕ}
    (h : TrieConf M ctx) :
    ConfinedTo M (bufWalkStepProg (ctx, st)) := by
  rcases ctx with ⟨⟨⟨mb, oc⟩, ⟨on_, oi⟩⟩, ⟨⟨pb, wv⟩, ⟨⟨ct, bc⟩, ⟨mn, qm⟩⟩⟩⟩
  rcases st with ⟨⟨found, cur⟩, remKey⟩
  obtain ⟨hw, hmn1, hM⟩ := h
  have hsub1 : ∀ addr, mb + oc ≤ addr → addr < mb + oc + packedWords (mn * 2 ^ bc) pb wv →
      M addr := fun addr h1 h2 => hM addr (Or.inl ⟨h1, h2⟩)
  have hch_lt : remKey &&& ((1 <<< bc) - 1) < 2 ^ bc := and_shiftLeft_mask_lt' remKey bc
  unfold bufWalkStepProg
  simp only [pure_bind]
  by_cases hcur : cur < mn
  · rw [ite_eq_left hcur]
    have hidx : (cur <<< bc) + (remKey &&& ((1 <<< bc) - 1)) < mn * 2 ^ bc :=
      child_idx_lt hcur hch_lt
    refine ConfinedTo.bind_prog (ConfinedTo.readPackedComp_prog hw hidx hsub1) fun _ => ?_
    exact ConfinedTo.ite_prog (fun _ => ConfinedTo.pure_prog _) fun _ =>
      ConfinedTo.ite_prog
        (fun _ => ConfinedTo.ite_prog (fun _ => ConfinedTo.pure_prog _)
          (fun _ => ConfinedTo.pure_prog _))
        (fun _ => ConfinedTo.pure_prog _)
  · rw [ite_eq_right hcur]
    have hidx0 : 0 < mn * 2 ^ bc := Nat.mul_pos hmn1 (Nat.two_pow_pos bc)
    refine ConfinedTo.bind_prog (ConfinedTo.readPackedComp_prog hw hidx0 hsub1) fun _ => ?_
    exact ConfinedTo.ite_prog (fun _ => ConfinedTo.pure_prog _) fun _ =>
      ConfinedTo.ite_prog
        (fun _ => ConfinedTo.ite_prog (fun _ => ConfinedTo.pure_prog _)
          (fun _ => ConfinedTo.pure_prog _))
        (fun _ => ConfinedTo.pure_prog _)

private theorem cf_bufWalkBoundedProg {M : ℕ → Prop} {ctx : TrieCtx} {rKey : ℕ}
    (h : TrieConf M ctx) :
    ConfinedTo M (bufWalkBoundedProg (ctx, rKey)) := by
  unfold bufWalkBoundedProg bufWalkLoopProg
  simp only [pure_bind]
  exact ConfinedTo.bind_prog
    (ConfinedTo.iterate_prog ctx (fun _ => cf_bufWalkStepProg h) _ _)
    fun _ => ConfinedTo.pure_prog _

/-- `bufLookupBoundedProg` is confined to `M` under `TrieConf M ctx`. -/
theorem confinedTo_bufLookupBoundedProg {M : ℕ → Prop} {ctx : TrieCtx} {rKey : ℕ}
    (h : TrieConf M ctx) :
    ConfinedTo M (bufLookupBoundedProg (ctx, rKey)) := by
  have h0 := h
  rcases ctx with ⟨⟨⟨mb, oc⟩, ⟨on_, oi⟩⟩, ⟨⟨pb, wv⟩, ⟨⟨ct, bc⟩, ⟨mn, qm⟩⟩⟩⟩
  obtain ⟨hw, _, hM⟩ := h
  have hsub2 : ∀ addr, mb + on_ ≤ addr → addr < mb + on_ + packedWords (6 * mn) pb wv → M addr :=
    fun addr h1 h2 => hM addr (Or.inr (Or.inl ⟨h1, h2⟩))
  have hsub3 : ∀ addr, mb + oi ≤ addr → addr < mb + oi + packedWords (6 * qm + 6) pb wv → M addr :=
    fun addr h1 h2 => hM addr (Or.inr (Or.inr ⟨h1, h2⟩))
  unfold bufLookupBoundedProg
  simp only [pure_bind]
  dsimp only [trieMb, trieOn, trieOi, triePb, trieWv, trieMn, trieQm]
  refine ConfinedTo.bind_prog (cf_bufWalkBoundedProg h0) fun _ => ?_
  refine ConfinedTo.ite_prog (fun _ => ConfinedTo.pure_prog _) fun _ => ?_
  refine ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ConfinedTo.pure_prog _)
  refine ConfinedTo.bind_prog (ConfinedTo.readPackedComp_prog hw (by omega) hsub2) fun _ => ?_
  refine ConfinedTo.bind_prog (ConfinedTo.readPackedComp_prog hw (by omega) hsub2) fun _ => ?_
  refine ConfinedTo.ite_prog (fun _ => ConfinedTo.pure_prog _) fun _ => ?_
  refine ConfinedTo.ite_prog (fun _ => ConfinedTo.pure_prog _) fun _ => ?_
  refine ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ConfinedTo.pure_prog _)
  exact ConfinedTo.bind_prog (ConfinedTo.readPackedComp_prog hw (by omega) hsub3) fun _ =>
    ConfinedTo.bind_prog (ConfinedTo.readPackedComp_prog hw (by omega) hsub3) fun _ =>
    ConfinedTo.pure_prog _

/-- `bufDeleteBoundedProg` is confined to `M` under `TrieConf M ctx`. -/
theorem confinedTo_bufDeleteBoundedProg {M : ℕ → Prop} {ctx : TrieCtx} {rKey : ℕ}
    (h : TrieConf M ctx) :
    ConfinedTo M (bufDeleteBoundedProg (ctx, rKey)) := by
  have h0 := h
  rcases ctx with ⟨⟨⟨mb, oc⟩, ⟨on_, oi⟩⟩, ⟨⟨pb, wv⟩, ⟨⟨ct, bc⟩, ⟨mn, qm⟩⟩⟩⟩
  obtain ⟨hw, _, hM⟩ := h
  have hsub2 : ∀ addr, mb + on_ ≤ addr → addr < mb + on_ + packedWords (6 * mn) pb wv → M addr :=
    fun addr h1 h2 => hM addr (Or.inr (Or.inl ⟨h1, h2⟩))
  unfold bufDeleteBoundedProg
  simp only [pure_bind]
  dsimp only [trieMb, trieOn, triePb, trieWv, trieMn]
  refine ConfinedTo.bind_prog (cf_bufWalkBoundedProg h0) fun _ => ?_
  refine ConfinedTo.ite_prog (fun _ => ConfinedTo.pure_prog _) fun _ => ?_
  refine ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ConfinedTo.pure_prog _)
  refine ConfinedTo.bind_prog (ConfinedTo.readPackedComp_prog hw (by omega) hsub2) fun _ => ?_
  refine ConfinedTo.bind_prog (ConfinedTo.readPackedComp_prog hw (by omega) hsub2) fun _ => ?_
  refine ConfinedTo.ite_prog (fun _ => ConfinedTo.pure_prog _) fun _ => ?_
  refine ConfinedTo.ite_prog (fun _ => ConfinedTo.pure_prog _) fun _ => ?_
  exact ConfinedTo.writePackedComp_prog hw (by omega) hsub2

private theorem cf_bufAllocNodeProg {M : ℕ → Prop} {ctx : TrieCtx} {cur ch : ℕ}
    (h : TrieConf M ctx) (hch : ch < 2 ^ (TrieLayout.ofCtx ctx).bChar) :
    ConfinedTo M (bufAllocNodeProg (ctx, (cur, ch))) := by
  rcases ctx with ⟨⟨⟨mb, oc⟩, ⟨on_, oi⟩⟩, ⟨⟨pb, wv⟩, ⟨⟨ct, bc⟩, ⟨mn, qm⟩⟩⟩⟩
  dsimp only [TrieLayout.ofCtx] at hch
  obtain ⟨hw, _, hM⟩ := h
  have hsub1 : ∀ addr, mb + oc ≤ addr → addr < mb + oc + packedWords (mn * 2 ^ bc) pb wv →
      M addr := fun addr h1 h2 => hM addr (Or.inl ⟨h1, h2⟩)
  have hsub2 : ∀ addr, mb + on_ ≤ addr → addr < mb + on_ + packedWords (6 * mn) pb wv → M addr :=
    fun addr h1 h2 => hM addr (Or.inr (Or.inl ⟨h1, h2⟩))
  have hsub3 : ∀ addr, mb + oi ≤ addr → addr < mb + oi + packedWords (6 * qm + 6) pb wv → M addr :=
    fun addr h1 h2 => hM addr (Or.inr (Or.inr ⟨h1, h2⟩))
  unfold bufAllocNodeProg
  refine ConfinedTo.bind_prog (ConfinedTo.readPackedComp_prog hw (by omega) hsub3) fun _ => ?_
  refine ConfinedTo.ite_prog (fun hcur => ?_) (fun _ => ConfinedTo.pure_prog _)
  refine ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ConfinedTo.pure_prog _)
  have hidx : (cur <<< bc) + ch < mn * 2 ^ bc := child_idx_lt hcur hch
  exact ConfinedTo.bind_prog (ConfinedTo.writePackedComp_prog hw hidx hsub1) fun _ =>
    ConfinedTo.bind_prog (ConfinedTo.writePackedComp_prog hw (by omega) hsub2) fun _ =>
    ConfinedTo.bind_prog (ConfinedTo.writePackedComp_prog hw (by omega) hsub2) fun _ =>
    ConfinedTo.bind_prog (ConfinedTo.writePackedComp_prog hw (by omega) hsub2) fun _ =>
    ConfinedTo.bind_prog (ConfinedTo.writePackedComp_prog hw (by omega) hsub3) fun _ =>
    ConfinedTo.pure_prog _

private theorem cf_bufEnsureStepProg {M : ℕ → Prop} {ctx : TrieCtx} {st : ℕ × ℕ}
    (h : TrieConf M ctx) :
    ConfinedTo M (bufEnsureStepProg (ctx, st)) := by
  have h0 := h
  rcases ctx with ⟨⟨⟨mb, oc⟩, ⟨on_, oi⟩⟩, ⟨⟨pb, wv⟩, ⟨⟨ct, bc⟩, ⟨mn, qm⟩⟩⟩⟩
  rcases st with ⟨cur, remKey⟩
  obtain ⟨hw, hmn1, hM⟩ := h
  have hsub1 : ∀ addr, mb + oc ≤ addr → addr < mb + oc + packedWords (mn * 2 ^ bc) pb wv →
      M addr := fun addr h1 h2 => hM addr (Or.inl ⟨h1, h2⟩)
  have hch_lt : remKey &&& ((1 <<< bc) - 1) < 2 ^ bc := and_shiftLeft_mask_lt' remKey bc
  unfold bufEnsureStepProg
  simp only [pure_bind]
  by_cases hcur : cur < mn
  · rw [ite_eq_left hcur]
    have hidx : (cur <<< bc) + (remKey &&& ((1 <<< bc) - 1)) < mn * 2 ^ bc :=
      child_idx_lt hcur hch_lt
    refine ConfinedTo.bind_prog (ConfinedTo.readPackedComp_prog hw hidx hsub1) fun _ => ?_
    refine ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ConfinedTo.pure_prog _)
    refine ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ConfinedTo.pure_prog _)
    exact ConfinedTo.bind_prog (cf_bufAllocNodeProg h0 hch_lt) fun _ => ConfinedTo.pure_prog _
  · rw [ite_eq_right hcur]
    have hidx0 : 0 < mn * 2 ^ bc := Nat.mul_pos hmn1 (Nat.two_pow_pos bc)
    refine ConfinedTo.bind_prog (ConfinedTo.readPackedComp_prog hw hidx0 hsub1) fun _ => ?_
    exact ConfinedTo.ite_prog (fun hc => absurd hc hcur) (fun _ => ConfinedTo.pure_prog _)

private theorem cf_bufAttachLeafProg {M : ℕ → Prop} {ctx : TrieCtx} {leaf bkt loc : ℕ}
    (h : TrieConf M ctx) :
    ConfinedTo M (bufAttachLeafProg (ctx, (leaf, (bkt, loc)))) := by
  rcases ctx with ⟨⟨⟨mb, oc⟩, ⟨on_, oi⟩⟩, ⟨⟨pb, wv⟩, ⟨⟨ct, bc⟩, ⟨mn, qm⟩⟩⟩⟩
  obtain ⟨hw, _, hM⟩ := h
  have hsub2 : ∀ addr, mb + on_ ≤ addr → addr < mb + on_ + packedWords (6 * mn) pb wv → M addr :=
    fun addr h1 h2 => hM addr (Or.inr (Or.inl ⟨h1, h2⟩))
  have hsub3 : ∀ addr, mb + oi ≤ addr → addr < mb + oi + packedWords (6 * qm + 6) pb wv → M addr :=
    fun addr h1 h2 => hM addr (Or.inr (Or.inr ⟨h1, h2⟩))
  unfold bufAttachLeafProg
  refine ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ConfinedTo.pure_prog _)
  refine ConfinedTo.bind_prog (ConfinedTo.readPackedComp_prog hw (by omega) hsub2) fun _ => ?_
  refine ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ?_)
  · refine ConfinedTo.bind_prog (ConfinedTo.readPackedComp_prog hw (by omega) hsub3) fun _ => ?_
    refine ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ConfinedTo.pure_prog _)
    exact ConfinedTo.bind_prog (ConfinedTo.writePackedComp_prog hw (by omega) hsub3) fun _ =>
      ConfinedTo.bind_prog (ConfinedTo.writePackedComp_prog hw (by omega) hsub2) fun _ =>
      ConfinedTo.bind_prog (ConfinedTo.writePackedComp_prog hw (by omega) hsub2) fun _ =>
      ConfinedTo.bind_prog (ConfinedTo.writePackedComp_prog hw (by omega) hsub3) fun _ =>
      ConfinedTo.bind_prog (ConfinedTo.writePackedComp_prog hw (by omega) hsub3) fun _ =>
      ConfinedTo.writePackedComp_prog hw (by omega) hsub3
  · simp only [pure_bind]
    refine ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ConfinedTo.pure_prog _)
    exact ConfinedTo.bind_prog (ConfinedTo.writePackedComp_prog hw (by omega) hsub2) fun _ =>
      ConfinedTo.bind_prog (ConfinedTo.writePackedComp_prog hw (by omega) hsub3) fun _ =>
      ConfinedTo.writePackedComp_prog hw (by omega) hsub3

/-- `bufInsertBoundedProg` is confined to `M` under `TrieConf M ctx`. -/
theorem confinedTo_bufInsertBoundedProg {M : ℕ → Prop} {ctx : TrieCtx} {rKey bkt loc : ℕ}
    (h : TrieConf M ctx) :
    ConfinedTo M (bufInsertBoundedProg (ctx, (rKey, (bkt, loc)))) := by
  unfold bufInsertBoundedProg bufEnsureLoopProg
  simp only [pure_bind]
  exact ConfinedTo.bind_prog
    (ConfinedTo.iterate_prog ctx (fun _ => cf_bufEnsureStepProg h) _ _)
    fun _ => cf_bufAttachLeafProg h

/-- `bufCheckSlotBoundedProg` is confined to `M` under `TrieConf M ctx`. -/
theorem confinedTo_bufCheckSlotBoundedProg {M : ℕ → Prop} {ctx : TrieCtx} {id : ℕ}
    (h : TrieConf M ctx) :
    ConfinedTo M (bufCheckSlotBoundedProg (ctx, id)) := by
  rcases ctx with ⟨⟨⟨mb, oc⟩, ⟨on_, oi⟩⟩, ⟨⟨pb, wv⟩, ⟨⟨ct, bc⟩, ⟨mn, qm⟩⟩⟩⟩
  obtain ⟨hw, _, hM⟩ := h
  have hsub2 : ∀ addr, mb + on_ ≤ addr → addr < mb + on_ + packedWords (6 * mn) pb wv → M addr :=
    fun addr h1 h2 => hM addr (Or.inr (Or.inl ⟨h1, h2⟩))
  have hsub3 : ∀ addr, mb + oi ≤ addr → addr < mb + oi + packedWords (6 * qm + 6) pb wv → M addr :=
    fun addr h1 h2 => hM addr (Or.inr (Or.inr ⟨h1, h2⟩))
  unfold bufCheckSlotBoundedProg
  refine ConfinedTo.bind_prog (ConfinedTo.readPackedComp_prog hw (by omega) hsub3) fun _ => ?_
  refine ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ConfinedTo.pure_prog _)
  refine ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ConfinedTo.pure_prog _)
  refine ConfinedTo.bind_prog (ConfinedTo.readPackedComp_prog hw (by omega) hsub3) fun _ => ?_
  refine ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ConfinedTo.pure_prog _)
  refine ConfinedTo.bind_prog (ConfinedTo.readPackedComp_prog hw (by omega) hsub2) fun _ =>
    ConfinedTo.bind_prog (ConfinedTo.readPackedComp_prog hw (by omega) hsub2) fun _ => ?_
  refine ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ConfinedTo.pure_prog _)
  refine ConfinedTo.ite_prog (fun _ => ConfinedTo.pure_prog _) fun _ => ?_
  exact ConfinedTo.bind_prog (ConfinedTo.readPackedComp_prog hw (by omega) hsub3) fun _ =>
    ConfinedTo.bind_prog (ConfinedTo.readPackedComp_prog hw (by omega) hsub3) fun _ =>
    ConfinedTo.pure_prog _

private theorem cf_bufClearOneBoundedProg {M : ℕ → Prop} {ctx : TrieCtx} {dummy : ℕ}
    (h : TrieConf M ctx) :
    ConfinedTo M (bufClearOneBoundedProg (ctx, dummy)) := by
  rcases ctx with ⟨⟨⟨mb, oc⟩, ⟨on_, oi⟩⟩, ⟨⟨pb, wv⟩, ⟨⟨ct, bc⟩, ⟨mn, qm⟩⟩⟩⟩
  obtain ⟨hw, hmn1, hM⟩ := h
  dsimp only [TrieLayout.ofCtx] at hw hmn1
  have hsub1 : ∀ addr, mb + oc ≤ addr → addr < mb + oc + packedWords (mn * 2 ^ bc) pb wv →
      M addr := fun addr h1 h2 => hM addr (Or.inl ⟨h1, h2⟩)
  have hsub2 : ∀ addr, mb + on_ ≤ addr → addr < mb + on_ + packedWords (6 * mn) pb wv → M addr :=
    fun addr h1 h2 => hM addr (Or.inr (Or.inl ⟨h1, h2⟩))
  have hsub3 : ∀ addr, mb + oi ≤ addr → addr < mb + oi + packedWords (6 * qm + 6) pb wv → M addr :=
    fun addr h1 h2 => hM addr (Or.inr (Or.inr ⟨h1, h2⟩))
  unfold bufClearOneBoundedProg
  refine ConfinedTo.bind_prog (ConfinedTo.readPackedComp_prog hw (by omega) hsub3) fun na => ?_
  refine ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ?_)
  · simp only [pure_bind]
    refine ConfinedTo.ite_prog (fun hu => ?_) (fun _ => ConfinedTo.pure_prog _)
    refine ConfinedTo.bind_prog (ConfinedTo.readPackedComp_prog hw (by omega) hsub2) fun p =>
      ConfinedTo.bind_prog (ConfinedTo.readPackedComp_prog hw (by omega) hsub2) fun ch => ?_
    have htail :
        ConfinedTo M
          (do
            writePackedCompGenProg ((((mb, on_), (pb, wv)), 6 * (na - 1) + 2), 0)
            writePackedCompGenProg ((((mb, oi), (pb, wv)), 6 * qm), na - 1)
            writePackedCompGenProg ((((mb, oi), (pb, wv)), 6 * qm + 1), 0)
            pure 0) :=
      by
        refine ConfinedTo.bind_prog
          (ConfinedTo.writePackedComp_prog hw (by omega) hsub2) fun _ => ?_
        refine ConfinedTo.bind_prog
          (ConfinedTo.writePackedComp_prog hw (by omega) hsub3) fun _ => ?_
        refine ConfinedTo.bind_prog
          (ConfinedTo.writePackedComp_prog hw (by omega) hsub3) fun _ => ?_
        exact ConfinedTo.pure_prog _
    exact ConfinedTo.ite_prog
      (fun hp => ConfinedTo.ite_prog
        (fun hch => ConfinedTo.bind_prog
          (ConfinedTo.writePackedComp_prog hw
            (child_idx_lt hp (by rwa [Nat.shiftLeft_eq, one_mul] at hch)) hsub1)
          fun _ => htail)
        (fun _ => htail))
      (fun _ => htail)
  · refine ConfinedTo.bind_prog (ConfinedTo.writePackedComp_prog hw (by omega) hsub3) fun _ => ?_
    refine ConfinedTo.bind_prog (ConfinedTo.writePackedComp_prog hw (by omega) hsub3) fun _ => ?_
    refine ConfinedTo.bind_prog (ConfinedTo.writePackedComp_prog hw (by omega) hsub2) fun _ => ?_
    exact ConfinedTo.pure_prog _

/-- `bufClearStepsBoundedProg` is confined to `M` under `TrieConf M ctx`. -/
theorem confinedTo_bufClearStepsBoundedProg {M : ℕ → Prop} {ctx : TrieCtx} {k : ℕ}
    (h : TrieConf M ctx) :
    ConfinedTo M (bufClearStepsBoundedProg (ctx, k)) := by
  unfold bufClearStepsBoundedProg bufClearLoopProg
  exact ConfinedTo.bind_prog
    (ConfinedTo.iterate_prog ctx (fun _ => cf_bufClearOneBoundedProg h) k 0)
    fun _ => ConfinedTo.pure_prog _

/-! ## Section 5: `LargeBlockPoolMetaProg` and `LargeBlockPoolStepProg` Confinement -/

/-- Bundle certifying that `ctx : BpMetaCtx` belongs to a valid `BpMetaLayout` whose owned metadata
addresses lie inside `M`. -/
@[expose] def BpMetaConf (M : ℕ → Prop) (ctx : BpMetaCtx) : Prop :=
  let mp := BpMetaLayout.ofCtx ctx
  0 < mp.w ∧ 16 * mp.M * mp.K ≤ 16 * mp.maxTail ∧ (∀ addr, mp.OwnsMetaAddr addr → M addr)

/-- `bpReadScalarProg` is confined to `M` under `BpMetaConf M ctx`. -/
theorem confinedTo_bpReadScalarProg {M : ℕ → Prop} {ctx : BpMetaCtx} {idx : ℕ}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpReadScalarProg (ctx, idx)) := by
  rcases ctx with ⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
    ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩
  dsimp only [BpMetaConf, BpMetaLayout.ofCtx, BpMetaLayout.OwnsMetaAddr] at h
  obtain ⟨_, _, hM⟩ := h
  unfold bpReadScalarProg
  refine ConfinedTo.ite_prog (fun hk => ?_) (fun _ => ConfinedTo.pure_prog _)
  exact ConfinedTo.read_prog (hM _ (by
    rcases hk with rfl | ⟨h1, h2⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨by omega, by omega⟩)))

/-- `bpWriteScalarProg` is confined to `M` under `BpMetaConf M ctx`. -/
theorem confinedTo_bpWriteScalarProg {M : ℕ → Prop} {ctx : BpMetaCtx} {idx val : ℕ}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpWriteScalarProg ((ctx, idx), val)) := by
  rcases ctx with ⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
    ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩
  dsimp only [BpMetaConf, BpMetaLayout.ofCtx, BpMetaLayout.OwnsMetaAddr] at h
  obtain ⟨_, _, hM⟩ := h
  unfold bpWriteScalarProg
  refine ConfinedTo.ite_prog (fun hcond => ?_) (fun _ => ConfinedTo.pure_prog _)
  exact ConfinedTo.write_prog (hM _ (by
    rcases hcond.1 with rfl | ⟨h1, h2⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨by omega, by omega⟩))) val

/-- `bpReadBktMetaProg` is confined to `M` under `BpMetaConf M ctx`. -/
private theorem confinedTo_bpReadBktMetaProg {M : ℕ → Prop} {ctx : BpMetaCtx} {b slot : ℕ}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpReadBktMetaProg (ctx, (b, slot))) := by
  rcases ctx with ⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
    ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩
  dsimp only [BpMetaConf, BpMetaLayout.ofCtx, BpMetaLayout.OwnsMetaAddr] at h
  obtain ⟨hw, _, hM⟩ := h
  unfold bpReadBktMetaProg
  refine ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ConfinedTo.pure_prog _)
  simp only [pure_bind]
  exact ConfinedTo.readPackedComp_prog hw (by omega) fun addr h1 h2 =>
    hM addr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))

/-- `bpWriteBktMetaProg` is confined to `M` under `BpMetaConf M ctx`. -/
private theorem confinedTo_bpWriteBktMetaProg {M : ℕ → Prop} {ctx : BpMetaCtx} {b slot val : ℕ}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpWriteBktMetaProg ((ctx, (b, slot)), val)) := by
  rcases ctx with ⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
    ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩
  dsimp only [BpMetaConf, BpMetaLayout.ofCtx, BpMetaLayout.OwnsMetaAddr] at h
  obtain ⟨hw, _, hM⟩ := h
  unfold bpWriteBktMetaProg
  refine ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ConfinedTo.pure_prog _)
  simp only [pure_bind]
  exact ConfinedTo.writePackedComp_prog hw (by omega) fun addr h1 h2 =>
    hM addr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))

private theorem cf_bpReadSlabOfProg {M : ℕ → Prop} {ctx : BpMetaCtx} {b v : ℕ}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpReadSlabOfProg (ctx, (b, v))) := by
  rcases ctx with ⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
    ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩
  dsimp only [BpMetaConf, BpMetaLayout.ofCtx, BpMetaLayout.OwnsMetaAddr] at h
  obtain ⟨hw, _, hM⟩ := h
  unfold bpReadSlabOfProg
  refine ConfinedTo.ite_prog (fun hcond => ?_) (fun _ => ConfinedTo.pure_prog _)
  simp only [pure_bind]
  exact ConfinedTo.readPackedComp_prog hw (slab_idx_lt hcond.1 hcond.2) fun addr h1 h2 =>
    hM addr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))))

private theorem cf_bpWriteSlabOfProg {M : ℕ → Prop} {ctx : BpMetaCtx} {b v val : ℕ}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpWriteSlabOfProg ((ctx, (b, v)), val)) := by
  rcases ctx with ⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
    ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩
  dsimp only [BpMetaConf, BpMetaLayout.ofCtx, BpMetaLayout.OwnsMetaAddr] at h
  obtain ⟨hw, _, hM⟩ := h
  unfold bpWriteSlabOfProg
  refine ConfinedTo.ite_prog (fun hcond => ?_) (fun _ => ConfinedTo.pure_prog _)
  simp only [pure_bind]
  exact ConfinedTo.writePackedComp_prog hw (slab_idx_lt hcond.1 hcond.2.1) fun addr h1 h2 =>
    hM addr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))))

/-- `bpReadTailDirRawProg` is confined to `M` under `BpMetaConf M ctx`. -/
theorem confinedTo_bpReadTailDirRawProg {M : ℕ → Prop} {ctx : BpMetaCtx} {idx : ℕ}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpReadTailDirRawProg (ctx, idx)) := by
  rcases ctx with ⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
    ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩
  dsimp only [BpMetaConf, BpMetaLayout.ofCtx, BpMetaLayout.OwnsMetaAddr] at h
  obtain ⟨hw, _, hM⟩ := h
  unfold bpReadTailDirRawProg
  refine ConfinedTo.ite_prog (fun hidx => ?_) (fun _ => ConfinedTo.pure_prog _)
  exact ConfinedTo.readPackedComp_prog hw hidx fun addr h1 h2 =>
    hM addr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))))

/-- `bpWriteTailDirRawProg` is confined to `M` under `BpMetaConf M ctx`. -/
theorem confinedTo_bpWriteTailDirRawProg {M : ℕ → Prop} {ctx : BpMetaCtx} {idx val : ℕ}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpWriteTailDirRawProg ((ctx, idx), val)) := by
  rcases ctx with ⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
    ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩
  dsimp only [BpMetaConf, BpMetaLayout.ofCtx, BpMetaLayout.OwnsMetaAddr] at h
  obtain ⟨hw, _, hM⟩ := h
  unfold bpWriteTailDirRawProg
  refine ConfinedTo.ite_prog (fun hcond => ?_) (fun _ => ConfinedTo.pure_prog _)
  exact ConfinedTo.writePackedComp_prog hw hcond.1 fun addr h1 h2 =>
    hM addr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))))

/-- `bpReadSlabOwnerProg` is confined to `M` under `BpMetaConf M ctx`. -/
theorem confinedTo_bpReadSlabOwnerProg {M : ℕ → Prop} {ctx : BpMetaCtx} {P lane : ℕ}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpReadSlabOwnerProg (ctx, (P, lane))) := by
  rcases ctx with ⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
    ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩
  dsimp only [BpMetaConf, BpMetaLayout.ofCtx, BpMetaLayout.OwnsMetaAddr] at h
  obtain ⟨hw, _, hM⟩ := h
  unfold bpReadSlabOwnerProg
  refine ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ConfinedTo.pure_prog _)
  simp only [pure_bind]
  exact ConfinedTo.readPackedComp_prog hw (by omega) fun addr h1 h2 =>
    hM addr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))))))

/-- `bpWriteSlabOwnerProg` is confined to `M` under `BpMetaConf M ctx`. -/
theorem confinedTo_bpWriteSlabOwnerProg {M : ℕ → Prop} {ctx : BpMetaCtx} {P lane val : ℕ}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpWriteSlabOwnerProg ((ctx, (P, lane)), val)) := by
  rcases ctx with ⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
    ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩
  dsimp only [BpMetaConf, BpMetaLayout.ofCtx, BpMetaLayout.OwnsMetaAddr] at h
  obtain ⟨hw, _, hM⟩ := h
  unfold bpWriteSlabOwnerProg
  refine ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ConfinedTo.pure_prog _)
  simp only [pure_bind]
  exact ConfinedTo.writePackedComp_prog hw (by omega) fun addr h1 h2 =>
    hM addr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))))))

private theorem cf_bpReadTailOwnerProg {M : ℕ → Prop} {ctx : BpMetaCtx} {t isRing : ℕ}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpReadTailOwnerProg (ctx, (t, isRing))) := by
  rcases ctx with ⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
    ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩
  dsimp only [BpMetaConf, BpMetaLayout.ofCtx, BpMetaLayout.OwnsMetaAddr] at h
  obtain ⟨hw, h16le, hM⟩ := h
  unfold bpReadTailOwnerProg
  refine ConfinedTo.ite_prog (fun ht => ?_) (fun _ => ConfinedTo.pure_prog _)
  simp only [pure_bind]
  exact ConfinedTo.readPackedComp_prog hw (tailOwner_idx_lt h16le ht isRing) fun addr h1 h2 =>
    hM addr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h2⟩))))))

private theorem cf_bpWriteTailOwnerProg {M : ℕ → Prop} {ctx : BpMetaCtx} {t isRing val : ℕ}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpWriteTailOwnerProg ((ctx, (t, isRing)), val)) := by
  rcases ctx with ⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
    ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩
  dsimp only [BpMetaConf, BpMetaLayout.ofCtx, BpMetaLayout.OwnsMetaAddr] at h
  obtain ⟨hw, h16le, hM⟩ := h
  unfold bpWriteTailOwnerProg
  refine ConfinedTo.ite_prog (fun hcond => ?_) (fun _ => ConfinedTo.pure_prog _)
  simp only [pure_bind]
  exact ConfinedTo.writePackedComp_prog hw (tailOwner_idx_lt h16le hcond.1 isRing) fun addr h1 h2 =>
    hM addr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h2⟩))))))

private theorem cf_bpBlkSlotProg (M : ℕ → Prop) (x : BpMetaCtx × (ℕ × ℕ)) :
    ConfinedTo M (bpBlkSlotProg x) := by
  rcases x with ⟨⟨_, ⟨⟨⟨_, _⟩, _⟩, ⟨_, _⟩⟩⟩, ⟨_, _⟩⟩
  unfold bpBlkSlotProg
  exact ConfinedTo.ite_prog (fun _ => ConfinedTo.pure_prog _) (fun _ => ConfinedTo.pure_prog _)

private theorem cf_bpTbSlotProg (M : ℕ → Prop) (x : BpMetaCtx × (ℕ × ℕ)) :
    ConfinedTo M (bpTbSlotProg x) := by
  rcases x with ⟨⟨_, ⟨⟨⟨_, _⟩, _⟩, _⟩⟩, ⟨_, _⟩⟩
  unfold bpTbSlotProg
  exact ConfinedTo.ite_prog (fun _ => ConfinedTo.pure_prog _) (fun _ => ConfinedTo.pure_prog _)

private theorem cf_bpTailRingIdxProg (M : ℕ → Prop) (x : BpMetaCtx × (ℕ × ℕ)) :
    ConfinedTo M (bpTailRingIdxProg x) := by
  rcases x with ⟨⟨_, ⟨⟨⟨_, _⟩, _⟩, _⟩⟩, ⟨_, _⟩⟩
  unfold bpTailRingIdxProg
  exact ConfinedTo.ite_prog (fun _ => ConfinedTo.pure_prog _) (fun _ => ConfinedTo.pure_prog _)

private theorem cf_bpRingAddProg (M : ℕ → Prop) (x : BpMetaCtx × (ℕ × ℕ)) :
    ConfinedTo M (bpRingAddProg x) := by
  rcases x with ⟨⟨_, ⟨⟨⟨_, _⟩, _⟩, _⟩⟩, ⟨_, _⟩⟩
  unfold bpRingAddProg
  exact ConfinedTo.ite_prog (fun _ => ConfinedTo.pure_prog _) (fun _ => ConfinedTo.pure_prog _)

/-- `bpDivModKProg` is confined to any `M` (pure arithmetic). -/
theorem confinedTo_bpDivModKProg (M : ℕ → Prop) (x : BpMetaCtx × ℕ) :
    ConfinedTo M (bpDivModKProg x) := by
  rcases x with ⟨⟨_, ⟨⟨⟨_, _⟩, _⟩, _⟩⟩, _⟩
  exact ConfinedTo.pure_prog _

private theorem cf_bpEffBlkProg {M : ℕ → Prop} {ctx : BpMetaCtx} {P off : ℕ}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpEffBlkProg (ctx, (P, off))) := by
  unfold bpEffBlkProg
  refine ConfinedTo.bind_prog (confinedTo_bpReadScalarProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpReadScalarProg h) fun _ => ?_
  refine ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ConfinedTo.pure_prog _)
  refine ConfinedTo.bind_prog (confinedTo_bpReadScalarProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpReadScalarProg h) fun _ => ?_
  exact ConfinedTo.ite_prog (fun _ => ConfinedTo.pure_prog _) fun _ =>
    ConfinedTo.ite_prog (fun _ => ConfinedTo.pure_prog _) (fun _ => ConfinedTo.pure_prog _)

private theorem cf_bpPhysOfTailProg {M : ℕ → Prop} {ctx : BpMetaCtx} {tIdx : ℕ}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpPhysOfTailProg (ctx, tIdx)) := by
  rcases ctx with ⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
    ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩
  unfold bpPhysOfTailProg
  simp only [pure_bind]
  refine ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ConfinedTo.pure_prog _)
  exact ConfinedTo.bind_prog (confinedTo_bpReadTailDirRawProg h) fun _ =>
    ConfinedTo.bind_prog (cf_bpEffBlkProg h) fun _ => cf_bpBlkSlotProg M _

private theorem cf_bpGetMKProg (M : ℕ → Prop) (ctx : BpMetaCtx) :
    ConfinedTo M (bpGetMKProg ctx) := by
  rcases ctx with ⟨_, ⟨⟨⟨_, _⟩, _⟩, _⟩⟩
  exact ConfinedTo.pure_prog _

private theorem cf_bpGetCapsProg (M : ℕ → Prop) (ctx : BpMetaCtx) :
    ConfinedTo M (bpGetCapsProg ctx) := by
  rcases ctx with ⟨_, ⟨⟨_, ⟨_, _⟩⟩, ⟨_, _⟩⟩⟩
  exact ConfinedTo.pure_prog _

private theorem cf_bpSubProg (M : ℕ → Prop) (xy : ℕ × ℕ) :
    ConfinedTo M (bpSubProg xy) := by
  rcases xy with ⟨_, _⟩
  unfold bpSubProg
  exact ConfinedTo.ite_prog (fun _ => ConfinedTo.pure_prog _) (fun _ => ConfinedTo.pure_prog _)

private theorem cf_bpWriteTailRingProg {M : ℕ → Prop} {ctx : BpMetaCtx} {b rk val : ℕ}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpWriteTailRingProg ((ctx, (b, rk)), val)) := by
  unfold bpWriteTailRingProg
  exact ConfinedTo.bind_prog (cf_bpTailRingIdxProg M _) fun _ =>
    confinedTo_bpWriteTailDirRawProg h

private theorem cf_bpWriteFreeTbStackProg {M : ℕ → Prop} {ctx : BpMetaCtx} {i val : ℕ}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpWriteFreeTbStackProg ((ctx, i), val)) := by
  unfold bpWriteFreeTbStackProg
  refine ConfinedTo.bind_prog (cf_bpGetMKProg M ctx) fun _ => ?_
  refine ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ConfinedTo.pure_prog _)
  simp only [pure_bind]
  exact confinedTo_bpWriteTailDirRawProg h

private theorem cf_bpWriteTbPhysBlkProg {M : ℕ → Prop} {ctx : BpMetaCtx} {tb val : ℕ}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpWriteTbPhysBlkProg ((ctx, tb), val)) := by
  unfold bpWriteTbPhysBlkProg
  refine ConfinedTo.bind_prog (cf_bpGetMKProg M ctx) fun _ => ?_
  refine ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ConfinedTo.pure_prog _)
  simp only [pure_bind]
  exact confinedTo_bpWriteTailDirRawProg h

private theorem cf_bpReadTailInfoProg {M : ℕ → Prop} {ctx : BpMetaCtx} {t : ℕ}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpReadTailInfoProg (ctx, t)) := by
  unfold bpReadTailInfoProg
  exact ConfinedTo.bind_prog (cf_bpPhysOfTailProg h) fun _ =>
    ConfinedTo.bind_prog (cf_bpReadTailOwnerProg h) fun _ =>
    ConfinedTo.bind_prog (cf_bpReadTailOwnerProg h) fun _ => ConfinedTo.pure_prog _

private theorem cf_bpSwapTailWriteProg {M : ℕ → Prop} {ctx : BpMetaCtx}
    {t₁ t₂ b₁ rk₁ b₂ rk₂ : ℕ} (h : BpMetaConf M ctx) :
    ConfinedTo M (bpSwapTailWriteProg ((ctx, (t₁, t₂)), ((b₁, rk₁), (b₂, rk₂)))) := by
  unfold bpSwapTailWriteProg
  exact ConfinedTo.bind_prog (cf_bpWriteTailRingProg h) fun _ =>
    ConfinedTo.bind_prog (cf_bpWriteTailRingProg h) fun _ =>
    ConfinedTo.bind_prog (cf_bpWriteTailOwnerProg h) fun _ =>
    ConfinedTo.bind_prog (cf_bpWriteTailOwnerProg h) fun _ =>
    ConfinedTo.bind_prog (cf_bpWriteTailOwnerProg h) fun _ => cf_bpWriteTailOwnerProg h

private theorem cf_bpSwapTailMetaProg {M : ℕ → Prop} {ctx : BpMetaCtx} {t₁ t₂ : ℕ}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpSwapTailMetaProg (ctx, (t₁, t₂))) := by
  unfold bpSwapTailMetaProg
  refine ConfinedTo.ite_prog (fun _ => ConfinedTo.pure_prog _) fun _ => ?_
  exact ConfinedTo.bind_prog (cf_bpReadTailInfoProg h) fun _ =>
    ConfinedTo.bind_prog (cf_bpReadTailInfoProg h) fun _ =>
    ConfinedTo.bind_prog (cf_bpSwapTailWriteProg h) fun _ => ConfinedTo.pure_prog _

private theorem cf_bpUnresRemoveAtProg {M : ℕ → Prop} {ctx : BpMetaCtx} {idx : ℕ}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpUnresRemoveAtProg (ctx, idx)) := by
  unfold bpUnresRemoveAtProg
  refine ConfinedTo.bind_prog (confinedTo_bpReadScalarProg h) fun _ =>
    ConfinedTo.bind_prog (cf_bpSubProg M _) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpReadSlabOwnerProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpWriteScalarProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpWriteSlabOwnerProg h) fun _ => ?_
  exact ConfinedTo.ite_prog (fun _ => confinedTo_bpWriteSlabOwnerProg h)
    (fun _ => ConfinedTo.pure_prog _)

private theorem cf_bpUnresPushProg {M : ℕ → Prop} {ctx : BpMetaCtx} {P : ℕ}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpUnresPushProg (ctx, P)) := by
  unfold bpUnresPushProg
  refine ConfinedTo.bind_prog (cf_bpGetCapsProg M ctx) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpReadScalarProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpWriteSlabOwnerProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpWriteSlabOwnerProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpWriteSlabOwnerProg h) fun _ => ?_
  simp only [pure_bind]
  exact confinedTo_bpWriteScalarProg h

private theorem cf_bpFreeTbProg {M : ℕ → Prop} {ctx : BpMetaCtx} {tb : ℕ}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpFreeTbProg (ctx, tb)) := by
  unfold bpFreeTbProg
  refine ConfinedTo.bind_prog (cf_bpGetCapsProg M ctx) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpReadScalarProg h) fun _ =>
    ConfinedTo.bind_prog (cf_bpWriteFreeTbStackProg h) fun _ => ?_
  simp only [pure_bind]
  exact confinedTo_bpWriteScalarProg h

private theorem cf_bpAllocTbPopProg {M : ℕ → Prop} {ctx : BpMetaCtx} {P top' : ℕ}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpAllocTbPopProg (ctx, (P, top'))) := by
  unfold bpAllocTbPopProg
  refine ConfinedTo.bind_prog (cf_bpGetMKProg M ctx) fun _ => ?_
  simp only [pure_bind]
  exact ConfinedTo.bind_prog (confinedTo_bpReadTailDirRawProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpWriteScalarProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpWriteSlabOwnerProg h) fun _ =>
    cf_bpWriteTbPhysBlkProg h

private theorem cf_bpAllocTbFreshProg {M : ℕ → Prop} {ctx : BpMetaCtx} {P : ℕ}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpAllocTbFreshProg (ctx, P)) := by
  unfold bpAllocTbFreshProg
  refine ConfinedTo.bind_prog (cf_bpGetCapsProg M ctx) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpReadScalarProg h) fun _ => ?_
  simp only [pure_bind]
  exact ConfinedTo.bind_prog (confinedTo_bpWriteScalarProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpWriteSlabOwnerProg h) fun _ =>
    cf_bpWriteTbPhysBlkProg h

private theorem cf_bpAllocTbForProg {M : ℕ → Prop} {ctx : BpMetaCtx} {P : ℕ}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpAllocTbForProg (ctx, P)) := by
  unfold bpAllocTbForProg
  refine ConfinedTo.bind_prog (confinedTo_bpReadScalarProg h) fun _ => ?_
  exact ConfinedTo.ite_prog (fun _ => cf_bpAllocTbPopProg h) (fun _ => cf_bpAllocTbFreshProg h)

private theorem cf_bpReadPromHdrProg {M : ℕ → Prop} {ctx : BpMetaCtx}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpReadPromHdrProg ctx) := by
  unfold bpReadPromHdrProg
  exact ConfinedTo.bind_prog (confinedTo_bpReadScalarProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpDivModKProg M _) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpReadScalarProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpReadScalarProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpReadScalarProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpReadScalarProg h) fun _ => ConfinedTo.pure_prog _

private theorem cf_bpCheckPromCandProg {M : ℕ → Prop} {ctx : BpMetaCtx} {i : ℕ}
    {hdr : (ℕ × ℕ) × (ℕ × (ℕ × ℕ))} (h : BpMetaConf M ctx) :
    ConfinedTo M (bpCheckPromCandProg ((ctx, i), hdr)) := by
  rcases hdr with ⟨⟨_, _⟩, ⟨_, ⟨_, _⟩⟩⟩
  unfold bpCheckPromCandProg
  refine ConfinedTo.bind_prog (confinedTo_bpReadSlabOwnerProg h) fun _ => ?_
  exact ConfinedTo.ite_prog (fun _ => ConfinedTo.pure_prog _) (fun _ => ConfinedTo.pure_prog _)

private theorem cf_bpFindPromoteIdxProg {M : ℕ → Prop} {ctx : BpMetaCtx}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpFindPromoteIdxProg ctx) := by
  unfold bpFindPromoteIdxProg
  refine ConfinedTo.bind_prog (cf_bpReadPromHdrProg h) fun _ =>
    ConfinedTo.bind_prog (cf_bpCheckPromCandProg h) fun _ => ?_
  refine ConfinedTo.ite_prog (fun _ => ConfinedTo.pure_prog _) fun _ => ?_
  refine ConfinedTo.bind_prog (cf_bpCheckPromCandProg h) fun _ => ?_
  refine ConfinedTo.ite_prog (fun _ => ConfinedTo.pure_prog _) fun _ => ?_
  refine ConfinedTo.bind_prog (cf_bpCheckPromCandProg h) fun _ => ?_
  refine ConfinedTo.ite_prog (fun _ => ConfinedTo.pure_prog _) fun _ => ?_
  refine ConfinedTo.bind_prog (cf_bpCheckPromCandProg h) fun _ => ?_
  exact ConfinedTo.ite_prog (fun _ => ConfinedTo.pure_prog _) (fun _ => ConfinedTo.pure_prog _)

private theorem cf_bpFindTopSwapIdxProg {M : ℕ → Prop} {ctx : BpMetaCtx}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpFindTopSwapIdxProg ctx) := by
  unfold bpFindTopSwapIdxProg
  refine ConfinedTo.bind_prog (confinedTo_bpReadScalarProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpDivModKProg M _) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpReadScalarProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpReadSlabOwnerProg h) fun _ => ?_
  refine ConfinedTo.ite_prog (fun _ => ConfinedTo.pure_prog _) fun _ => ?_
  refine ConfinedTo.bind_prog (confinedTo_bpReadSlabOwnerProg h) fun _ => ?_
  exact ConfinedTo.ite_prog (fun _ => ConfinedTo.pure_prog _) (fun _ => ConfinedTo.pure_prog _)

private theorem cf_bpStartPromoteProg {M : ℕ → Prop} {ctx : BpMetaCtx} {b : ℕ}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpStartPromoteProg (ctx, b)) := by
  unfold bpStartPromoteProg
  exact ConfinedTo.bind_prog (cf_bpFindPromoteIdxProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpReadSlabOwnerProg h) fun _ =>
    ConfinedTo.bind_prog (cf_bpUnresRemoveAtProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpWriteSlabOwnerProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpWriteSlabOwnerProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpWriteBktMetaProg h) fun _ =>
    confinedTo_bpWriteBktMetaProg h

private theorem cf_bpStartDemoteReadProg {M : ℕ → Prop} {ctx : BpMetaCtx} {b vp : ℕ}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpStartDemoteReadProg (ctx, (b, vp))) := by
  unfold bpStartDemoteReadProg
  exact ConfinedTo.bind_prog (cf_bpGetMKProg M ctx) fun _ =>
    ConfinedTo.bind_prog (cf_bpReadSlabOfProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpReadBktMetaProg h) fun _ =>
    ConfinedTo.bind_prog (cf_bpRingAddProg M _) fun _ => ConfinedTo.pure_prog _

private theorem cf_bpStartDemoteWriteAProg {M : ℕ → Prop} {ctx : BpMetaCtx}
    {b P_act vp r_b : ℕ} (h : BpMetaConf M ctx) :
    ConfinedTo M (bpStartDemoteWriteAProg ((ctx, b), (P_act, (vp, r_b)))) := by
  unfold bpStartDemoteWriteAProg
  refine ConfinedTo.bind_prog (cf_bpGetMKProg M ctx) fun _ =>
    ConfinedTo.bind_prog (cf_bpAllocTbForProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpWriteBktMetaProg h) fun _ => ?_
  simp only [pure_bind]
  exact confinedTo_bpWriteBktMetaProg h

private theorem cf_bpStartDemoteWriteBProg {M : ℕ → Prop} {ctx : BpMetaCtx}
    {b P_act hd_new : ℕ} (h : BpMetaConf M ctx) :
    ConfinedTo M (bpStartDemoteWriteBProg ((ctx, b), (P_act, hd_new))) := by
  unfold bpStartDemoteWriteBProg
  refine ConfinedTo.bind_prog (cf_bpGetMKProg M ctx) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpWriteBktMetaProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpWriteBktMetaProg h) fun _ => ?_
  simp only [pure_bind]
  exact ConfinedTo.bind_prog (confinedTo_bpWriteBktMetaProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpWriteSlabOwnerProg h) fun _ =>
    confinedTo_bpWriteSlabOwnerProg h

private theorem cf_bpStartDemoteProg {M : ℕ → Prop} {ctx : BpMetaCtx} {b q_b r_b : ℕ}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpStartDemoteProg (ctx, (b, (q_b, r_b)))) := by
  unfold bpStartDemoteProg
  refine ConfinedTo.bind_prog (cf_bpSubProg M _) fun _ =>
    ConfinedTo.bind_prog (cf_bpStartDemoteReadProg h) fun ph => ?_
  rcases ph with ⟨_, _⟩
  exact ConfinedTo.bind_prog (cf_bpStartDemoteWriteAProg h) fun _ =>
    cf_bpStartDemoteWriteBProg h

private theorem cf_bpMaybeStartTryDemoteProg {M : ℕ → Prop} {ctx : BpMetaCtx} {b q_b r_b : ℕ}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpMaybeStartTryDemoteProg (ctx, (b, (q_b, r_b)))) := by
  unfold bpMaybeStartTryDemoteProg
  refine ConfinedTo.bind_prog (cf_bpGetMKProg M ctx) fun _ => ?_
  exact ConfinedTo.ite_prog (fun _ => cf_bpStartDemoteProg h) (fun _ => ConfinedTo.pure_prog _)

private theorem cf_bpMaybeStartIdleProg {M : ℕ → Prop} {ctx : BpMetaCtx} {b : ℕ}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpMaybeStartIdleProg (ctx, b)) := by
  unfold bpMaybeStartIdleProg
  refine ConfinedTo.bind_prog (cf_bpGetMKProg M ctx) fun _ =>
    ConfinedTo.bind_prog (cf_bpGetCapsProg M ctx) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpReadBktMetaProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpReadBktMetaProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpReadScalarProg h) fun _ => ?_
  exact ConfinedTo.ite_prog (fun _ => cf_bpStartPromoteProg h)
    (fun _ => cf_bpMaybeStartTryDemoteProg h)

private theorem cf_bpMaybeStartMetaProg {M : ℕ → Prop} {ctx : BpMetaCtx} {b : ℕ}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpMaybeStartMetaProg (ctx, b)) := by
  unfold bpMaybeStartMetaProg
  refine ConfinedTo.bind_prog (confinedTo_bpReadBktMetaProg h) fun _ => ?_
  exact ConfinedTo.ite_prog (fun _ => ConfinedTo.pure_prog _)
    (fun _ => cf_bpMaybeStartIdleProg h)

private theorem cf_bpActPromCoordsProg {M : ℕ → Prop} {ctx : BpMetaCtx} {b cur : ℕ}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpActPromCoordsProg ((ctx, b), cur)) := by
  unfold bpActPromCoordsProg
  exact ConfinedTo.bind_prog (confinedTo_bpReadBktMetaProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpReadSlabOwnerProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpReadBktMetaProg h) fun _ =>
    ConfinedTo.bind_prog (cf_bpRingAddProg M _) fun _ =>
    ConfinedTo.bind_prog (cf_bpTailRingIdxProg M _) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpReadTailDirRawProg h) fun _ =>
    ConfinedTo.bind_prog (cf_bpTbSlotProg M _) fun _ => ConfinedTo.pure_prog _

private theorem cf_bpActPromFinAProg {M : ℕ → Prop} {ctx : BpMetaCtx} {b P_act : ℕ}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpActPromFinAProg ((ctx, b), P_act)) := by
  unfold bpActPromFinAProg
  refine ConfinedTo.bind_prog (cf_bpGetCapsProg M ctx) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpReadBktMetaProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpReadSlabOwnerProg h) fun _ =>
    ConfinedTo.bind_prog (cf_bpFreeTbProg h) fun _ => ?_
  simp only [pure_bind]
  exact ConfinedTo.bind_prog (confinedTo_bpWriteBktMetaProg h) fun _ => ConfinedTo.pure_prog _

private theorem cf_bpActPromFinCProg {M : ℕ → Prop} {ctx : BpMetaCtx} {b P_act vp : ℕ}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpActPromFinCProg ((ctx, b), (P_act, vp))) := by
  unfold bpActPromFinCProg
  exact ConfinedTo.bind_prog (confinedTo_bpWriteBktMetaProg h) fun _ =>
    ConfinedTo.bind_prog (cf_bpWriteSlabOfProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpWriteSlabOwnerProg h) fun _ =>
    confinedTo_bpWriteSlabOwnerProg h

private theorem cf_bpActPromFinBProg {M : ℕ → Prop} {ctx : BpMetaCtx} {b P_act vp : ℕ}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpActPromFinBProg ((ctx, b), (P_act, vp))) := by
  unfold bpActPromFinBProg
  exact ConfinedTo.bind_prog (cf_bpGetMKProg M ctx) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpReadBktMetaProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpReadBktMetaProg h) fun _ =>
    ConfinedTo.bind_prog (cf_bpRingAddProg M _) fun _ =>
    ConfinedTo.bind_prog (cf_bpSubProg M _) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpWriteBktMetaProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpWriteBktMetaProg h) fun _ =>
    cf_bpActPromFinCProg h

private theorem cf_bpActPromoteRunProg {M : ℕ → Prop} {ctx : BpMetaCtx} {b ac : ℕ}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpActPromoteRunProg ((ctx, b), ac)) := by
  unfold bpActPromoteRunProg
  refine ConfinedTo.bind_prog (cf_bpGetMKProg M ctx) fun _ =>
    ConfinedTo.bind_prog (cf_bpSubProg M _) fun _ =>
    ConfinedTo.bind_prog (cf_bpActPromCoordsProg h) fun coords => ?_
  rcases coords with ⟨_, ⟨_, _⟩⟩
  refine ConfinedTo.bind_prog (cf_bpSwapTailMetaProg h) fun _ => ?_
  refine ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ?_)
  · simp only [pure_bind]
    exact ConfinedTo.bind_prog (confinedTo_bpWriteBktMetaProg h) fun _ => ConfinedTo.pure_prog _
  · exact ConfinedTo.bind_prog (cf_bpActPromFinAProg h) fun _ =>
      ConfinedTo.bind_prog (cf_bpActPromFinBProg h) fun _ => ConfinedTo.pure_prog _

private theorem cf_bpActPromoteStepProg {M : ℕ → Prop} {ctx : BpMetaCtx} {b ac : ℕ}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpActPromoteStepProg ((ctx, b), ac)) := by
  unfold bpActPromoteStepProg
  refine ConfinedTo.bind_prog (confinedTo_bpReadBktMetaProg h) fun _ =>
    ConfinedTo.bind_prog (cf_bpSubProg M _) fun _ => ?_
  exact ConfinedTo.ite_prog (fun _ => ConfinedTo.pure_prog _)
    (fun _ => cf_bpActPromoteRunProg h)

private theorem cf_bpActDemoteBaseProg {M : ℕ → Prop} {ctx : BpMetaCtx} {b cur' : ℕ}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpActDemoteBaseProg ((ctx, b), cur')) := by
  unfold bpActDemoteBaseProg
  exact ConfinedTo.bind_prog (confinedTo_bpReadBktMetaProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpReadSlabOwnerProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpReadBktMetaProg h) fun _ =>
    ConfinedTo.bind_prog (cf_bpRingAddProg M _) fun _ =>
    ConfinedTo.bind_prog (cf_bpTbSlotProg M _) fun _ =>
    ConfinedTo.bind_prog (cf_bpWriteTailRingProg h) fun _ =>
    ConfinedTo.bind_prog (cf_bpWriteTailOwnerProg h) fun _ =>
    ConfinedTo.bind_prog (cf_bpWriteTailOwnerProg h) fun _ => ConfinedTo.pure_prog _

private theorem cf_bpActDemoteStepProg {M : ℕ → Prop} {ctx : BpMetaCtx} {b ac : ℕ}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpActDemoteStepProg ((ctx, b), ac)) := by
  unfold bpActDemoteStepProg
  refine ConfinedTo.bind_prog (cf_bpGetMKProg M ctx) fun _ =>
    ConfinedTo.bind_prog (cf_bpSubProg M _) fun _ =>
    ConfinedTo.bind_prog (cf_bpSubProg M _) fun _ =>
    ConfinedTo.bind_prog (cf_bpActDemoteBaseProg h) fun _ => ?_
  refine ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ?_)
  · exact ConfinedTo.bind_prog (cf_bpSubProg M _) fun _ =>
      ConfinedTo.bind_prog (confinedTo_bpWriteBktMetaProg h) fun _ => ConfinedTo.pure_prog _
  · exact ConfinedTo.bind_prog (cf_bpUnresPushProg h) fun _ =>
      ConfinedTo.bind_prog (confinedTo_bpWriteBktMetaProg h) fun _ => ConfinedTo.pure_prog _

private theorem cf_bpActStepMetaProg {M : ℕ → Prop} {ctx : BpMetaCtx} {b : ℕ}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpActStepMetaProg (ctx, b)) := by
  unfold bpActStepMetaProg
  refine ConfinedTo.bind_prog (cf_bpGetMKProg M ctx) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpReadBktMetaProg h) fun _ => ?_
  refine ConfinedTo.ite_prog (fun _ => ConfinedTo.pure_prog _) fun _ => ?_
  exact ConfinedTo.ite_prog (fun _ => cf_bpActPromoteStepProg h)
    (fun _ => cf_bpActDemoteStepProg h)

/-- `bpBktTickMetaProg` is confined to `M` under `BpMetaConf M ctx`. -/
theorem confinedTo_bpBktTickMetaProg {M : ℕ → Prop} {ctx : BpMetaCtx} {b : ℕ}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpBktTickMetaProg (ctx, b)) := by
  unfold bpBktTickMetaProg
  exact ConfinedTo.bind_prog (cf_bpMaybeStartMetaProg h) fun _ => cf_bpActStepMetaProg h

private theorem cf_bpCommitTopSwapReadProg {M : ℕ → Prop} {ctx : BpMetaCtx}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpCommitTopSwapReadProg ctx) := by
  unfold bpCommitTopSwapReadProg
  exact ConfinedTo.bind_prog (confinedTo_bpReadScalarProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpReadScalarProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpReadSlabOwnerProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpReadSlabOwnerProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpReadSlabOwnerProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpReadSlabOwnerProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpReadSlabOwnerProg h) fun _ => ConfinedTo.pure_prog _

private theorem cf_bpCommitTopSwapBaseAProg {M : ℕ → Prop} {ctx : BpMetaCtx} {S D tagS : ℕ}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpCommitTopSwapBaseAProg (ctx, ((S, D), tagS))) := by
  unfold bpCommitTopSwapBaseAProg
  exact ConfinedTo.bind_prog (confinedTo_bpWriteScalarProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpWriteScalarProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpWriteSlabOwnerProg h) fun _ =>
    confinedTo_bpWriteSlabOwnerProg h

private theorem cf_bpCommitTopSwapBaseBProg {M : ℕ → Prop} {ctx : BpMetaCtx}
    {S D m1S m2S posD tbD : ℕ} (h : BpMetaConf M ctx) :
    ConfinedTo M (bpCommitTopSwapBaseBProg (ctx, ((S, D), ((m1S, m2S), (posD, tbD))))) := by
  unfold bpCommitTopSwapBaseBProg
  exact ConfinedTo.bind_prog (confinedTo_bpWriteSlabOwnerProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpWriteSlabOwnerProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpWriteSlabOwnerProg h) fun _ =>
    confinedTo_bpWriteSlabOwnerProg h

private theorem cf_bpCommitTopSwapPtrsProg {M : ℕ → Prop} {ctx : BpMetaCtx}
    {info : (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × (ℕ × ℕ)))} (h : BpMetaConf M ctx) :
    ConfinedTo M (bpCommitTopSwapPtrsProg (ctx, info)) := by
  rcases info with ⟨⟨_, _⟩, ⟨⟨_, _⟩, ⟨_, ⟨_, _⟩⟩⟩⟩
  unfold bpCommitTopSwapPtrsProg
  refine ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ?_)
  · exact ConfinedTo.bind_prog (confinedTo_bpWriteSlabOwnerProg h) fun _ =>
      ConfinedTo.bind_prog (confinedTo_bpWriteSlabOwnerProg h) fun _ =>
      ConfinedTo.bind_prog (cf_bpWriteTbPhysBlkProg h) fun _ =>
      cf_bpWriteTbPhysBlkProg h
  · refine ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ?_)
    · exact ConfinedTo.bind_prog (cf_bpWriteSlabOfProg h) fun _ =>
        ConfinedTo.bind_prog (confinedTo_bpWriteSlabOwnerProg h) fun _ =>
        cf_bpWriteTbPhysBlkProg h
    · exact ConfinedTo.bind_prog (confinedTo_bpWriteBktMetaProg h) fun _ =>
        ConfinedTo.bind_prog (confinedTo_bpWriteSlabOwnerProg h) fun _ =>
        ConfinedTo.bind_prog (cf_bpWriteTbPhysBlkProg h) fun _ =>
        cf_bpWriteTbPhysBlkProg h

private theorem cf_bpCommitTopSwapMetaProg {M : ℕ → Prop} {ctx : BpMetaCtx}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpCommitTopSwapMetaProg ctx) := by
  unfold bpCommitTopSwapMetaProg
  refine ConfinedTo.bind_prog (cf_bpCommitTopSwapReadProg h) fun info => ?_
  rcases info with ⟨⟨_, _⟩, ⟨⟨_, _⟩, ⟨_, ⟨_, _⟩⟩⟩⟩
  exact ConfinedTo.bind_prog (cf_bpCommitTopSwapBaseAProg h) fun _ =>
    ConfinedTo.bind_prog (cf_bpCommitTopSwapBaseBProg h) fun _ =>
    cf_bpCommitTopSwapPtrsProg h

private theorem cf_bpTopSwapReadSwProg {M : ℕ → Prop} {ctx : BpMetaCtx}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpTopSwapReadSwProg ctx) := by
  unfold bpTopSwapReadSwProg
  exact ConfinedTo.bind_prog (confinedTo_bpReadScalarProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpReadScalarProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpReadScalarProg h) fun _ =>
    ConfinedTo.bind_prog (cf_bpBlkSlotProg M _) fun _ =>
    ConfinedTo.bind_prog (cf_bpBlkSlotProg M _) fun _ => ConfinedTo.pure_prog _

private theorem cf_bpTopSwapStepMetaProg {M : ℕ → Prop} {ctx : BpMetaCtx}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpTopSwapStepMetaProg ctx) := by
  unfold bpTopSwapStepMetaProg
  refine ConfinedTo.bind_prog (confinedTo_bpReadScalarProg h) fun _ => ?_
  refine ConfinedTo.ite_prog (fun _ => ConfinedTo.pure_prog _) fun _ => ?_
  refine ConfinedTo.bind_prog (cf_bpGetMKProg M ctx) fun _ =>
    ConfinedTo.bind_prog (cf_bpTopSwapReadSwProg h) fun _ => ?_
  refine ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ?_)
  · exact ConfinedTo.bind_prog (confinedTo_bpWriteScalarProg h) fun _ => ConfinedTo.pure_prog _
  · exact ConfinedTo.bind_prog (cf_bpCommitTopSwapMetaProg h) fun _ => ConfinedTo.pure_prog _

private theorem cf_bpTopCleanActProg {M : ℕ → Prop} {ctx : BpMetaCtx} {P : ℕ}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpTopCleanActProg (ctx, P)) := by
  unfold bpTopCleanActProg
  refine ConfinedTo.bind_prog (confinedTo_bpReadScalarProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpReadScalarProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpReadSlabOwnerProg h) fun _ => ?_
  exact ConfinedTo.ite_prog (fun _ => cf_bpTopSwapStepMetaProg h)
    (fun _ => ConfinedTo.pure_prog _)

private theorem cf_bpStartTopSwapProg {M : ℕ → Prop} {ctx : BpMetaCtx} {P : ℕ}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpStartTopSwapProg (ctx, P)) := by
  unfold bpStartTopSwapProg
  exact ConfinedTo.bind_prog (cf_bpFindTopSwapIdxProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpReadSlabOwnerProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpWriteScalarProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpWriteScalarProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpWriteScalarProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpWriteScalarProg h) fun _ =>
    cf_bpTopSwapStepMetaProg h

private theorem cf_bpTopCleanIdleProg {M : ℕ → Prop} {ctx : BpMetaCtx} {P : ℕ}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpTopCleanIdleProg (ctx, P)) := by
  unfold bpTopCleanIdleProg
  refine ConfinedTo.bind_prog (confinedTo_bpReadSlabOwnerProg h) fun _ => ?_
  refine ConfinedTo.ite_prog (fun _ => ConfinedTo.pure_prog _) fun _ => ?_
  refine ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ?_)
  · exact ConfinedTo.bind_prog (confinedTo_bpReadSlabOwnerProg h) fun _ =>
      cf_bpActStepMetaProg h
  · refine ConfinedTo.bind_prog (confinedTo_bpReadScalarProg h) fun _ => ?_
    exact ConfinedTo.ite_prog (fun _ => cf_bpStartTopSwapProg h)
      (fun _ => ConfinedTo.pure_prog _)

/-- `bpTopCleanMetaProg` is confined to `M` under `BpMetaConf M ctx`. -/
theorem confinedTo_bpTopCleanMetaProg {M : ℕ → Prop} {ctx : BpMetaCtx}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpTopCleanMetaProg ctx) := by
  unfold bpTopCleanMetaProg
  refine ConfinedTo.bind_prog (confinedTo_bpReadScalarProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpDivModKProg M _) fun _ => ?_
  refine ConfinedTo.ite_prog (fun _ => ConfinedTo.pure_prog _) fun _ => ?_
  simp only [pure_bind]
  refine ConfinedTo.bind_prog (confinedTo_bpReadScalarProg h) fun _ => ?_
  exact ConfinedTo.ite_prog (fun _ => cf_bpTopCleanActProg h)
    (fun _ => cf_bpTopCleanIdleProg h)

private theorem cf_bpPrepPopEndProg {M : ℕ → Prop} {ctx : BpMetaCtx} {b : ℕ}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpPrepPopEndProg (ctx, b)) := by
  unfold bpPrepPopEndProg
  exact ConfinedTo.bind_prog (confinedTo_bpReadBktMetaProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpReadBktMetaProg h) fun _ =>
    ConfinedTo.bind_prog (cf_bpSubProg M _) fun _ =>
    ConfinedTo.bind_prog (cf_bpRingAddProg M _) fun _ =>
    ConfinedTo.bind_prog (cf_bpTailRingIdxProg M _) fun _ =>
    confinedTo_bpReadTailDirRawProg h

private theorem cf_bpPrepPopTopProg {M : ℕ → Prop} {ctx : BpMetaCtx}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpPrepPopTopProg ctx) := by
  unfold bpPrepPopTopProg
  refine ConfinedTo.bind_prog (cf_bpGetMKProg M ctx) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpReadScalarProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpDivModKProg M _) fun _ => ?_
  refine ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ?_)
  · exact ConfinedTo.bind_prog (confinedTo_bpReadSlabOwnerProg h) fun _ => cf_bpTbSlotProg M _
  · exact ConfinedTo.bind_prog (cf_bpSubProg M _) fun _ =>
      ConfinedTo.bind_prog (confinedTo_bpReadSlabOwnerProg h) fun _ => cf_bpTbSlotProg M _

/-- `bpPrepPopMetaProg` is confined to `M` under `BpMetaConf M ctx`. -/
theorem confinedTo_bpPrepPopMetaProg {M : ℕ → Prop} {ctx : BpMetaCtx} {b : ℕ}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpPrepPopMetaProg (ctx, b)) := by
  unfold bpPrepPopMetaProg
  exact ConfinedTo.bind_prog (cf_bpPrepPopEndProg h) fun _ =>
    ConfinedTo.bind_prog (cf_bpPrepPopTopProg h) fun _ =>
    cf_bpSwapTailMetaProg h

private theorem cf_bpCommitPopShrinkProg {M : ℕ → Prop} {ctx : BpMetaCtx} {b ns r_b : ℕ}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpCommitPopShrinkProg ((ctx, b), (ns, r_b))) := by
  unfold bpCommitPopShrinkProg
  exact ConfinedTo.bind_prog (cf_bpSubProg M _) fun _ =>
    ConfinedTo.bind_prog (cf_bpSubProg M _) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpWriteScalarProg h) fun _ =>
    confinedTo_bpWriteBktMetaProg h

private theorem cf_bpCommitPopCase2CleanProg {M : ℕ → Prop} {ctx : BpMetaCtx} {bf : ℕ}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpCommitPopCase2CleanProg (ctx, bf)) := by
  unfold bpCommitPopCase2CleanProg
  exact ConfinedTo.bind_prog (confinedTo_bpReadSlabOwnerProg h) fun _ =>
    ConfinedTo.bind_prog (cf_bpSubProg M _) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpReadSlabOwnerProg h) fun _ =>
    ConfinedTo.bind_prog (cf_bpFreeTbProg h) fun _ =>
    cf_bpUnresRemoveAtProg h

/-- `bpCommitPopMetaProg` is confined to `M` under `BpMetaConf M ctx`. -/
theorem confinedTo_bpCommitPopMetaProg {M : ℕ → Prop} {ctx : BpMetaCtx} {b : ℕ}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpCommitPopMetaProg (ctx, b)) := by
  unfold bpCommitPopMetaProg
  refine ConfinedTo.bind_prog (confinedTo_bpReadScalarProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpDivModKProg M _) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpReadBktMetaProg h) fun _ => ?_
  refine ConfinedTo.ite_prog (fun _ => cf_bpCommitPopShrinkProg h) fun _ => ?_
  exact ConfinedTo.bind_prog (cf_bpCommitPopCase2CleanProg h) fun _ =>
    cf_bpCommitPopShrinkProg h

/-- `bpTbSlotProg` is confined to any `M` (pure arithmetic). -/
theorem confinedTo_bpTbSlotProg (M : ℕ → Prop) (x : BpMetaCtx × (ℕ × ℕ)) :
    ConfinedTo M (bpTbSlotProg x) :=
  cf_bpTbSlotProg M x

/-- `bpRingDiffProg` is confined to any `M` (pure arithmetic). -/
private theorem confinedTo_bpRingDiffProg (M : ℕ → Prop) (x : BpMetaCtx × (ℕ × ℕ)) :
    ConfinedTo M (bpRingDiffProg x) := by
  rcases x with ⟨⟨_, ⟨⟨⟨_, _⟩, _⟩, _⟩⟩, ⟨_, _⟩⟩
  unfold bpRingDiffProg
  exact ConfinedTo.ite_prog (fun _ => ConfinedTo.pure_prog _) (fun _ => ConfinedTo.pure_prog _)

/-- `bpBktLocProg` is confined to any `M` (pure arithmetic). -/
private theorem confinedTo_bpBktLocProg (M : ℕ → Prop) (x : BpMetaCtx × (ℕ × ℕ)) :
    ConfinedTo M (bpBktLocProg x) := by
  rcases x with ⟨⟨_, ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, _⟩⟩, ⟨_, _⟩⟩
  unfold bpBktLocProg
  exact ConfinedTo.ite_prog (fun _ => ConfinedTo.pure_prog _) (fun _ => ConfinedTo.pure_prog _)

/-- `bpReadTailOwnerProg` is confined to `M` under `BpMetaConf M ctx`. -/
theorem confinedTo_bpReadTailOwnerProg {M : ℕ → Prop} {ctx : BpMetaCtx} {t isRing : ℕ}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpReadTailOwnerProg (ctx, (t, isRing))) :=
  cf_bpReadTailOwnerProg h

/-- `bpReadBktCountProg` is confined to `M` under `BpMetaConf M ctx`. -/
theorem confinedTo_bpReadBktCountProg {M : ℕ → Prop} {ctx : BpMetaCtx} {b : ℕ}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpReadBktCountProg (ctx, b)) := by
  unfold bpReadBktCountProg
  exact ConfinedTo.bind_prog (confinedTo_bpReadBktMetaProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpReadBktMetaProg h) fun _ =>
    confinedTo_bpBktLocProg M _

/-- `bpActCurProg` is confined to `M` under `BpMetaConf M ctx`. -/
theorem confinedTo_bpActCurProg {M : ℕ → Prop} {ctx : BpMetaCtx} {b : ℕ}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpActCurProg (ctx, b)) := by
  rcases ctx with ⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
    ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩
  unfold bpActCurProg
  refine ConfinedTo.bind_prog (confinedTo_bpReadBktMetaProg h) fun _ => ?_
  exact ConfinedTo.ite_prog (fun _ => ConfinedTo.pure_prog _) fun _ =>
    ConfinedTo.ite_prog (fun _ => ConfinedTo.pure_prog _) (fun _ => ConfinedTo.pure_prog _)

private theorem cf_bpToPhysRemProg {M : ℕ → Prop} {ctx : BpMetaCtx} {b k_rem : ℕ}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpToPhysRemProg (ctx, (b, k_rem))) := by
  unfold bpToPhysRemProg
  refine ConfinedTo.bind_prog (confinedTo_bpActCurProg h) fun _ => ?_
  refine ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ?_)
  · exact ConfinedTo.bind_prog (confinedTo_bpReadBktMetaProg h) fun _ =>
      ConfinedTo.bind_prog (cf_bpEffBlkProg h) fun _ => cf_bpBlkSlotProg M _
  · exact ConfinedTo.bind_prog (confinedTo_bpReadBktMetaProg h) fun _ =>
      ConfinedTo.bind_prog (cf_bpRingAddProg M _) fun _ =>
      ConfinedTo.bind_prog (cf_bpTailRingIdxProg M _) fun _ =>
      ConfinedTo.bind_prog (confinedTo_bpReadTailDirRawProg h) fun _ =>
      cf_bpPhysOfTailProg h

/-- `bpToPhysProg` is confined to `M` under `BpMetaConf M ctx`. -/
theorem confinedTo_bpToPhysProg {M : ℕ → Prop} {ctx : BpMetaCtx} {b loc : ℕ}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpToPhysProg (ctx, (b, loc))) := by
  unfold bpToPhysProg
  refine ConfinedTo.bind_prog (confinedTo_bpReadBktMetaProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpBktLocProg M _) fun _ => ?_
  refine ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ?_)
  · exact ConfinedTo.bind_prog (confinedTo_bpDivModKProg M _) fun _ =>
      ConfinedTo.bind_prog (cf_bpReadSlabOfProg h) fun _ =>
      ConfinedTo.bind_prog (cf_bpEffBlkProg h) fun _ => cf_bpBlkSlotProg M _
  · simp only [pure_bind]; exact cf_bpToPhysRemProg h

private theorem cf_bpOwnerOfTailProg {M : ℕ → Prop} {ctx : BpMetaCtx} {tIdx : ℕ}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpOwnerOfTailProg (ctx, tIdx)) := by
  unfold bpOwnerOfTailProg
  exact ConfinedTo.bind_prog (cf_bpReadTailOwnerProg h) fun _ =>
    ConfinedTo.bind_prog (cf_bpReadTailOwnerProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpReadBktMetaProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpReadBktMetaProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpRingDiffProg M _) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpBktLocProg M _) fun _ =>
    ConfinedTo.pure_prog _

private theorem cf_bpOwnerOfNonSlabProg {M : ℕ → Prop} {ctx : BpMetaCtx} {P off tag : ℕ}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpOwnerOfNonSlabProg (ctx, ((P, off), tag))) := by
  unfold bpOwnerOfNonSlabProg
  refine ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ?_)
  · refine ConfinedTo.bind_prog (confinedTo_bpReadSlabOwnerProg h) fun _ =>
      ConfinedTo.bind_prog (confinedTo_bpActCurProg h) fun _ => ?_
    refine ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ?_)
    · exact ConfinedTo.bind_prog (confinedTo_bpReadBktMetaProg h) fun _ =>
        ConfinedTo.bind_prog (confinedTo_bpBktLocProg M _) fun _ =>
        ConfinedTo.pure_prog _
    · exact ConfinedTo.bind_prog (confinedTo_bpReadSlabOwnerProg h) fun _ =>
        ConfinedTo.bind_prog (cf_bpTbSlotProg M _) fun _ =>
        cf_bpOwnerOfTailProg h
  · exact ConfinedTo.bind_prog (confinedTo_bpReadSlabOwnerProg h) fun _ =>
      ConfinedTo.bind_prog (cf_bpTbSlotProg M _) fun _ =>
      cf_bpOwnerOfTailProg h

private theorem cf_bpAppendReadTopProg {M : ℕ → Prop} {ctx : BpMetaCtx}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpAppendReadTopProg ctx) := by
  unfold bpAppendReadTopProg
  exact ConfinedTo.bind_prog (confinedTo_bpReadScalarProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpDivModKProg M _) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpReadSlabOwnerProg h) fun _ =>
    ConfinedTo.bind_prog (cf_bpTbSlotProg M _) fun _ =>
    ConfinedTo.pure_prog _

private theorem cf_bpAppendWriteBaseProg {M : ℕ → Prop} {ctx : BpMetaCtx}
    {b ns r_b t_new rk_new : ℕ} (h : BpMetaConf M ctx) :
    ConfinedTo M (bpAppendWriteBaseProg ((ctx, b), ((ns, r_b), (t_new, rk_new)))) := by
  unfold bpAppendWriteBaseProg
  refine ConfinedTo.bind_prog (cf_bpGetMKProg M ctx) fun _ =>
    ConfinedTo.bind_prog (cf_bpGetCapsProg M ctx) fun _ => ?_
  simp only [pure_bind]
  exact ConfinedTo.bind_prog (confinedTo_bpWriteScalarProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpWriteBktMetaProg h) fun _ =>
    ConfinedTo.bind_prog (cf_bpWriteTailRingProg h) fun _ =>
    ConfinedTo.bind_prog (cf_bpWriteTailOwnerProg h) fun _ =>
    cf_bpWriteTailOwnerProg h

private theorem cf_bpAdvanceTopBlkProg {M : ℕ → Prop} {ctx : BpMetaCtx} {bf : ℕ}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpAdvanceTopBlkProg (ctx, bf)) := by
  unfold bpAdvanceTopBlkProg
  refine ConfinedTo.bind_prog (cf_bpGetCapsProg M ctx) fun _ => ?_
  simp only [pure_bind]
  exact ConfinedTo.bind_prog (cf_bpUnresPushProg h) fun _ =>
    ConfinedTo.bind_prog (cf_bpAllocTbForProg h) fun _ =>
    confinedTo_bpWriteSlabOwnerProg h

/-- `bpRawPostAppendMetaProg` is confined to `M` under `BpMetaConf M ctx`. -/
theorem confinedTo_bpRawPostAppendMetaProg {M : ℕ → Prop} {ctx : BpMetaCtx} {b : ℕ}
    (h : BpMetaConf M ctx) :
    ConfinedTo M (bpRawPostAppendMetaProg (ctx, b)) := by
  unfold bpRawPostAppendMetaProg
  refine ConfinedTo.bind_prog (cf_bpGetMKProg M ctx) fun _ =>
    ConfinedTo.bind_prog (cf_bpAppendReadTopProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpReadBktMetaProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpReadBktMetaProg h) fun _ =>
    ConfinedTo.bind_prog (cf_bpRingAddProg M _) fun _ =>
    ConfinedTo.bind_prog (cf_bpAppendWriteBaseProg h) fun _ => ?_
  exact ConfinedTo.ite_prog (fun _ => ConfinedTo.pure_prog _) (fun _ => cf_bpAdvanceTopBlkProg h)

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

end
