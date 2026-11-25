/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.Dynamic.Spec
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.DualEpochStep
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.DualEpochSplitFrame
-- Unfolds `epochInitZeroedProg` to lift `GoodEpochAt` without prior `mem metaBase = N`.
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpoch
-- Unfolds `fastInitZeroedProg` to prove `[metaBase, metaBase + offPageDir)` write confinement.
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpochSubEpoch
import CslibFrontier.Computability.WordRAM.Realization.BoundedTactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Dual-Epoch State Invariants and Uniform Slot API (`DualEpochInvBase`)

This module defines the coupled resting (`DualStateInv`) and mid-step (`DualMidInv`) state
invariants and uniform epoch-slot specifications for the 12-phase (`0..11`) deamortized dual-epoch
resizable succinct worst-case WHP dictionary ([Bender, Farach-Colton, J. Kuszmaul, and W. Kuszmaul,
SOSA 2024, Sections 5–6][BenderFarachColtonKuszmaulKuszmaul2024]):

1. **Abstract two-slot dictionary algebra (`toDictState`, `DisjointOpt`, `orOpt`):**
   Relates `Fin U → Option (Fin V)` slot maps and disjoint migration overlays `orOpt s_dst s_src`
   to `Dictionary.State U` (`Dynamic.spec U V U`) and `Dictionary.dom` cardinalities.
2. **Uniform small/large `EpochSlotInv` API (`SlotLatent`, `EpochSlotInv`):**
   Bundles small (`nCap = 0`) and large (`whpThreshold c ≤ nCap`) epoch slots—both active
   (`draining = false`, carrying `GoodEpochAt`) and draining (`draining = true` in Phase `8`,
   carrying latched `SlotLatent.GoodCovers → mode = 0` with frozen pre-migration `evs`)—behind a
   uniform specification interface (`query_spec`, `insert_spec`, `delete_spec`, `popAny_spec`,
   `transfer_io`, `update_nCap`).
3. **Root initializer (`initDualRootProg`) and 12-phase countdown budget (`remRebuildBudget`):**
   Provides the `RealizesBounded .exact` (`¬ReadsWidth`) 194-word empty-arena initializer and the
   monotone countdown budget proving `16 * (elapsed + 2) ≤ max (whpThreshold c) nSrc`.
4. **Coupled invariants (`DualCoreInv`, `DualStateInv`, `DualMidInv`):**
   Packages the 12-phase root-header, hardware-frontier, and active/draining slot invariants
   (foreground query and mutation specifications are proved in `DualEpochInvQuery` and
   `DualEpochInvFG*`).

## Main definitions

* `toDictState`: embeds `Fin U → Option (Fin V)` into `Dictionary.State U`.
* `DisjointOpt`: domain disjointness between active migration slots `s_dst` and `s_src`.
* `orOpt`: overlay dictionary map `(s_dst u).or (s_src u)` during Phase `8` (`migrate`).
* `SlotLatent`: non-dependent latent per-slot state `(nCap, s_abs, seeds, evs)`.
* `EpochSlotInv`: unified small (`nCap = 0`) and large (`whpThreshold c ≤ nCap`) slot invariant.
* `initDualRootProg`: `RealizesBounded .exact` (`¬ReadsWidth`) root-arena initializer.
* `remRebuildBudget`: 12-phase countdown tick budget bounded by `max (whpThreshold c) nSrc / 16`.
* `DualLatent`: latent dual-epoch state `(slotSrc, slotDst, nTrig, trigOps, elapsed, unpermBound)`.
* `DualStateInv`: resting 12-phase dual-epoch memory and frontier invariant.
* `DualMidInv`: mid-operation dual-epoch invariant between `userMutateProg` and `bgTickProg`.

## Main results

* `GoodEpochAt.of_initZeroed`: `epochInitZeroedProg` establishes `GoodEpochAt` at `evs = []`.
* `epochInitZeroedProg_meta_confine`: `epochInitZeroedProg` modifies only
  `[metaBase, metaBase + offPageDir)`.
* `dualStateInv_init`: `initDualRootProg` establishes `DualStateInv` for `Dictionary.empty U`.

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
open EpochUpdate

attribute [local simp] Realization.memoryCost_bind'
attribute [local simp] prog_clientResult_bind prog_runClient_state_bind prog_clientResult_pure
attribute [local simp] prog_runClient_state_pure prog_clientResult_map prog_runClient_state_map
attribute [local simp] prog_memoryCost_map prog_clientResult_read prog_runClient_state_read
attribute [local simp] prog_memoryCost_read prog_clientResult_write prog_runClient_state_write
attribute [local simp] prog_memoryCost_write

/-! ## Section 1: Abstract Two-Slot Dictionary Algebra (`toDictState`, `DisjointOpt`, `orOpt`) -/

/-- Embeds a typed `Fin U → Option (Fin V)` map into `Dictionary.State U` (`Fin U → Option ℕ`). -/
@[expose] def toDictState {U V : ℕ} (s_abs : Fin U → Option (Fin V)) : Dictionary.State U :=
  fun u => (s_abs u).map Fin.val

@[simp] theorem toDictState_empty (U V : ℕ) :
    toDictState (fun _ : Fin U => (none : Option (Fin V))) = Dictionary.empty U := rfl

theorem toDictState_insert {U V : ℕ} (s_abs : Fin U → Option (Fin V)) (u : Fin U) (v : Fin V) :
    toDictState (Function.update s_abs u (some v)) =
      Function.update (toDictState s_abs) u (some v.val) := by
  funext x
  by_cases h : x = u
  · subst h; simp [toDictState]
  · simp [toDictState, Function.update_of_ne h]

theorem toDictState_delete {U V : ℕ} (s_abs : Fin U → Option (Fin V)) (u : Fin U) :
    toDictState (Function.update s_abs u none) =
      Function.update (toDictState s_abs) u none := by
  funext x
  by_cases h : x = u
  · subst h; simp [toDictState]
  · simp [toDictState, Function.update_of_ne h]

theorem dom_toDictState_eq {U V : ℕ} (s_abs : Fin U → Option (Fin V)) :
    Dictionary.dom (toDictState s_abs) = liveDom s_abs := by
  classical
  unfold Dictionary.dom liveDom toDictState
  ext u
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  cases s_abs u <;> simp

theorem dom_toDictState_card {U V : ℕ} (s_abs : Fin U → Option (Fin V)) :
    (Dictionary.dom (toDictState s_abs)).card = (liveDom s_abs).card := by
  rw [dom_toDictState_eq]

theorem liveDom_card_le_U {U V : ℕ} (s_abs : Fin U → Option (Fin V)) :
    (liveDom s_abs).card ≤ U := by
  classical
  calc (liveDom s_abs).card ≤ (Finset.univ : Finset (Fin U)).card := Finset.card_filter_le _ _
    _ = U := Fintype.card_fin U

theorem liveDom_eq_univ_of_card_eq {U V : ℕ} {s_abs : Fin U → Option (Fin V)}
    (hc : (liveDom s_abs).card = U) (u : Fin U) : s_abs u ≠ none := by
  classical
  have huniv : liveDom s_abs = Finset.univ :=
    Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      (by rw [Finset.card_univ, Fintype.card_fin U, hc])
  exact (mem_liveDom_iff _ _).mp (huniv ▸ Finset.mem_univ u)

theorem liveDom_insert_card {U V : ℕ} (s_abs : Fin U → Option (Fin V)) (u : Fin U) (v : Fin V) :
    (liveDom (Function.update s_abs u (some v))).card =
      if s_abs u = none then (liveDom s_abs).card + 1 else (liveDom s_abs).card := by
  classical
  have heq : liveDom (Function.update s_abs u (some v)) = insert u (liveDom s_abs) := by
    ext x
    simp only [mem_liveDom_iff, Finset.mem_insert]
    by_cases hx : x = u
    · subst hx; simp
    · simp [hx]
  rw [heq]
  by_cases h : s_abs u = none
  · rw [ite_eq_left h, Finset.card_insert_of_notMem]
    simp [mem_liveDom_iff, h]
  · rw [ite_eq_right h, Finset.insert_eq_of_mem]
    simpa [mem_liveDom_iff] using h

theorem liveDom_delete_card {U V : ℕ} (s_abs : Fin U → Option (Fin V)) (u : Fin U) :
    (liveDom (Function.update s_abs u none)).card =
      if s_abs u = none then (liveDom s_abs).card else (liveDom s_abs).card - 1 := by
  classical
  have heq : liveDom (Function.update s_abs u none) = (liveDom s_abs).erase u := by
    ext x
    simp only [mem_liveDom_iff, Finset.mem_erase]
    by_cases hx : x = u
    · subst hx; simp
    · simp [hx]
  rw [heq]
  by_cases h : s_abs u = none
  · rw [ite_eq_left h, Finset.erase_eq_of_notMem]
    simp [mem_liveDom_iff, h]
  · rw [ite_eq_right h, Finset.card_erase_of_mem]
    simpa [mem_liveDom_iff] using h

/-- Domain disjointness between destination map `s_dst` and source map `s_src` in Phase `8`. -/
@[expose] def DisjointOpt {U V : ℕ} (s_dst s_src : Fin U → Option (Fin V)) : Prop :=
  ∀ u, s_dst u = none ∨ s_src u = none

/-- Overlay map `(s_dst u).or (s_src u)` representing the logical dictionary during Phase `8`. -/
@[expose] def orOpt {U V : ℕ} (s_dst s_src : Fin U → Option (Fin V)) : Fin U → Option (Fin V) :=
  fun u => (s_dst u).or (s_src u)

@[simp] theorem orOpt_empty_left {U V : ℕ} (s_src : Fin U → Option (Fin V)) :
    orOpt (fun _ : Fin U => (none : Option (Fin V))) s_src = s_src := by
  funext u; rfl

@[simp] theorem orOpt_empty_right {U V : ℕ} (s_dst : Fin U → Option (Fin V)) :
    orOpt s_dst (fun _ : Fin U => (none : Option (Fin V))) = s_dst := by
  funext u; unfold orOpt; cases s_dst u <;> rfl

theorem disjointOpt_empty_left {U V : ℕ} (s_src : Fin U → Option (Fin V)) :
    DisjointOpt (fun _ : Fin U => (none : Option (Fin V))) s_src :=
  fun _ => Or.inl rfl

theorem liveDom_orOpt_card {U V : ℕ} {s_dst s_src : Fin U → Option (Fin V)}
    (hdj : DisjointOpt s_dst s_src) :
    (liveDom (orOpt s_dst s_src)).card = (liveDom s_dst).card + (liveDom s_src).card := by
  classical
  have hunion : liveDom (orOpt s_dst s_src) = liveDom s_dst ∪ liveDom s_src := by
    ext u
    simp only [mem_liveDom_iff, Finset.mem_union, orOpt]
    cases s_dst u <;> cases s_src u <;> simp
  have hdisj : Disjoint (liveDom s_dst) (liveDom s_src) := by
    rw [Finset.disjoint_left]
    intro u hd hs
    rw [mem_liveDom_iff] at hd hs
    rcases hdj u with h | h
    · exact hd h
    · exact hs h
  rw [hunion, Finset.card_union_of_disjoint hdisj]

theorem disjointOpt_delete_src_card_lt {U V : ℕ} {s_dst s_src : Fin U → Option (Fin V)}
    (hdj : DisjointOpt s_dst s_src) {u : Fin U} (hdst_none : s_dst u = none) :
    (liveDom (Function.update s_src u none)).card + (liveDom s_dst).card ≤
      (liveDom (orOpt s_dst s_src)).card ∧
    (liveDom (Function.update s_src u none)).card + (liveDom s_dst).card < U := by
  classical
  have hdj' : DisjointOpt s_dst (Function.update s_src u none) := fun x => by
    by_cases hx : x = u
    · subst hx; exact Or.inr (Function.update_self ..)
    · rw [Function.update_of_ne hx]; exact hdj x
  have hsum : (liveDom (Function.update s_src u none)).card + (liveDom s_dst).card =
      (liveDom (orOpt s_dst (Function.update s_src u none))).card := by
    rw [liveDom_orOpt_card hdj', add_comm]
  rw [hsum]
  have hsub1 : liveDom (orOpt s_dst (Function.update s_src u none)) ⊆
      liveDom (orOpt s_dst s_src) := by
    intro x hx
    rw [mem_liveDom_iff] at hx ⊢
    by_cases hxu : x = u
    · subst hxu; simp [orOpt, hdst_none] at hx
    · simpa [orOpt, Function.update_of_ne hxu] using hx
  have hsub2 : liveDom (orOpt s_dst (Function.update s_src u none)) ⊆ Finset.univ.erase u := by
    intro x hx
    rw [mem_liveDom_iff] at hx
    rw [Finset.mem_erase]
    refine ⟨fun hxu => ?_, Finset.mem_univ x⟩
    subst hxu; simp [orOpt, hdst_none] at hx
  have hltU : (Finset.univ.erase u).card < U := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ, Fintype.card_fin U]
    exact Nat.sub_lt (Nat.zero_lt_of_lt u.isLt) Nat.one_pos
  exact ⟨Finset.card_le_card hsub1, (Finset.card_le_card hsub2).trans_lt hltU⟩

theorem orOpt_insert_dst_delete_src {U V : ℕ} (s_dst s_src : Fin U → Option (Fin V))
    (hdj : DisjointOpt s_dst s_src) (u : Fin U) (v : Fin V) :
    orOpt (Function.update s_dst u (some v)) (Function.update s_src u none) =
      Function.update (orOpt s_dst s_src) u (some v) ∧
    DisjointOpt (Function.update s_dst u (some v)) (Function.update s_src u none) := by
  refine ⟨funext fun x => ?_, fun x => ?_⟩
  · by_cases hx : x = u
    · subst hx; simp [orOpt]
    · simp [orOpt, Function.update_of_ne hx]
  · by_cases hx : x = u
    · subst hx; exact Or.inr (Function.update_self ..)
    · rw [Function.update_of_ne hx, Function.update_of_ne hx]; exact hdj x

theorem orOpt_delete_both {U V : ℕ} (s_dst s_src : Fin U → Option (Fin V))
    (hdj : DisjointOpt s_dst s_src) (u : Fin U) :
    orOpt (Function.update s_dst u none) (Function.update s_src u none) =
      Function.update (orOpt s_dst s_src) u none ∧
    DisjointOpt (Function.update s_dst u none) (Function.update s_src u none) := by
  refine ⟨funext fun x => ?_, fun x => ?_⟩
  · by_cases hx : x = u
    · subst hx; simp [orOpt]
    · simp [orOpt, Function.update_of_ne hx]
  · by_cases hx : x = u
    · subst hx; exact Or.inl (Function.update_self ..)
    · rw [Function.update_of_ne hx, Function.update_of_ne hx]; exact hdj x

theorem orOpt_migrate_pop_insert {U V : ℕ} {s_dst s_src : Fin U → Option (Fin V)}
    (hdj : DisjointOpt s_dst s_src) {u : Fin U} {v : Fin V} (hsrc : s_src u = some v) :
    s_dst u = none ∧
    orOpt (Function.update s_dst u (some v)) (Function.update s_src u none) = orOpt s_dst s_src ∧
    DisjointOpt (Function.update s_dst u (some v)) (Function.update s_src u none) := by
  have hdst : s_dst u = none := by
    rcases hdj u with h | h
    · exact h
    · rw [hsrc] at h; cases h
  refine ⟨hdst, funext fun x => ?_, fun x => ?_⟩
  · by_cases hx : x = u
    · subst hx; simp [orOpt, hdst, hsrc]
    · simp [orOpt, Function.update_of_ne hx]
  · by_cases hx : x = u
    · subst hx; exact Or.inr (Function.update_self ..)
    · rw [Function.update_of_ne hx, Function.update_of_ne hx]; exact hdj x

theorem evs_card_nil (U V nCap : ℕ) :
    ∀ k ≤ ([] : List (EpochUpdate U V)).length,
      (liveDom (EpochUpdate.eval (([] : List (EpochUpdate U V)).take k))).card ≤ nCap := by
  intro k hk
  simp only [List.length_nil, Nat.le_zero] at hk
  subst hk
  have hempty : liveDom (fun _ : Fin U => (none : Option (Fin V))) = ∅ := by
    classical ext x; simp [liveDom]
  simp [hempty]

theorem evs_card_append {U V nCap : ℕ} {evs : List (EpochUpdate U V)}
    (hprev : ∀ k ≤ evs.length, (liveDom (EpochUpdate.eval (evs.take k))).card ≤ nCap)
    (ev : EpochUpdate U V)
    (hlast : (liveDom (EpochUpdate.eval (evs ++ [ev]))).card ≤ nCap) :
    ∀ k ≤ (evs ++ [ev]).length,
      (liveDom (EpochUpdate.eval ((evs ++ [ev]).take k))).card ≤ nCap := by
  intro k hk
  rw [List.length_append, List.length_singleton] at hk
  by_cases hle : k ≤ evs.length
  · rw [List.take_append_of_le_length hle]; exact hprev k hle
  · have heq : k = evs.length + 1 := by omega
    subst heq
    rw [List.take_of_length_le (by simp)]
    exact hlast

/-! ## Section 2: `epochInitZeroedProg` Metadata Confinement & `GoodEpochAt.of_initZeroed` -/

/-- `epochInitZeroedProg fl.pBase` modifies only `[fl.metaBase, fl.metaBase + offPageDir)`, leaving
all item-stream, `ParamTable`, and partner-epoch words intact. -/
theorem epochInitZeroedProg_meta_confine {fl : FastEpochLayout} {w : ℕ} {s : Memory.State}
    (hr : FastLayoutReady w fl s) :
    let s' := (Memory.spec 0).clientState s (epochInitZeroedProg fl.pBase)
    ∀ addr, ¬(fl.metaBase ≤ addr ∧ addr < fl.metaBase + offPageDir fl.c fl.w fl.N) →
      s'.mem addr = s.mem addr := by
  dsimp only
  have hv := hr.1
  have hpt := hr.2.1
  have hN_pos : 0 < fl.N := lt_of_lt_of_le (whpThreshold_pos fl.c) hv.thresh_le
  have hm0 : s.mem fl.pBase = fl.N := hpt 0 (by decide)
  have hm1 : s.mem (fl.pBase + 1) = fl.metaBase := hpt 1 (by decide)
  set s1 : Memory.State := { mem := Function.update s.mem fl.metaBase fl.N, frontier := s.frontier }
  have hstep : (Memory.spec 0).clientState s (epochInitZeroedProg fl.pBase) =
      (Memory.spec 0).clientState s1 (fastInitZeroedProg fl.pBase) := by
    unfold epochInitZeroedProg
    rw [StateTransitionSpec.clientState_bind, cstate_rd, cres_rd, hm0,
      StateTransitionSpec.clientState_bind, cstate_rd, cres_rd, hm1,
      ite_eq_right hN_pos.ne', StateTransitionSpec.clientState_bind]
    rfl
  have hr1 : FastLayoutReady w fl s1 := by
    refine ⟨hv, hpt.congr fun a h1 _ => ?_, ?_, ?_⟩
    · exact Function.update_of_ne (by have := hv.pBase_lt_meta; omega) _ _
    · dsimp only [s1]
      rw [Function.update_of_ne (by
        dsimp only [FastEpochLayout.bktHashBase]; unfold offBktHash; omega)]
      exact hr.2.2.1
    · dsimp only [s1]
      rw [Function.update_of_ne (by
        dsimp only [FastEpochLayout.fpHashBase]; unfold offFpHash offBktHash; omega)]
      exact hr.2.2.2
  obtain ⟨_, hr2, _, hout_bp⟩ := fastBpInitProg_ready hr1
  obtain ⟨_, hr3, _, hres2⟩ := fastBufInitEmptyProg_ready (role := 0) hr2
  obtain ⟨_, hout_t0⟩ := hres2 (by decide)
  obtain ⟨_, _, _, hres3⟩ := fastBufInitEmptyProg_ready (role := 1) hr3
  obtain ⟨_, hout_t1⟩ := hres3 (by decide)
  intro addr hnot
  have hmv := hv.mp_valid
  have hn_bp : ¬fl.mp.OwnsMetaAddr addr := fun hm => hnot <| by
    rcases BpMetaLayout.OwnsMetaAddr.bounds hmv hm with (rfl | ⟨h10, h17⟩) | ⟨hlo, hhi⟩
    · dsimp only [FastEpochLayout.mp, epochBpMetaLayout]
      refine ⟨by omega, ?_⟩
      unfold offPageDir offTrieItem offTrieNode offTrieChild offBTreeVals offBTreeKeys
        offBTreeMeta offTailOwner offSlabOwner offTailDir offSlabDir offBktMeta offFpHash
        offBktHash; omega
    · dsimp only [FastEpochLayout.mp, epochBpMetaLayout] at h10 h17
      refine ⟨by omega, ?_⟩
      unfold offPageDir offTrieItem offTrieNode offTrieChild offBTreeVals offBTreeKeys
        offBTreeMeta offTailOwner offSlabOwner offTailDir offSlabDir offBktMeta offFpHash
        offBktHash; omega
    · dsimp only [FastEpochLayout.mp, epochBpMetaLayout] at hlo hhi
      refine ⟨by omega, ?_⟩
      unfold offPageDir offTrieItem offTrieNode offTrieChild offBTreeVals offBTreeKeys offBTreeMeta
      omega
  have hn_tr : ∀ r < 2, ¬(fl.trieL r).OwnsAddr addr := fun r hr_lt ht => hnot <| by
    have hm := offTrie_mono (c := fl.c) (w := fl.w) (N := fl.N) hr_lt
    dsimp only [FastEpochLayout.trieL, epochTrieLayout, TrieLayout.OwnsAddr] at ht
    rcases ht with h1 | h2 | h3 <;> exact ⟨by omega, by omega⟩
  rw [hstep]; unfold fastInitZeroedProg
  rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
    hout_t1 addr (hn_tr 1 (by decide)), hout_t0 addr (hn_tr 0 (by decide)), hout_bp addr hn_bp]
  exact Function.update_of_ne (fun he => hnot ⟨by omega, by
    unfold offPageDir offTrieItem offTrieNode offTrieChild offBTreeVals offBTreeKeys
      offBTreeMeta offTailOwner offSlabOwner offTailDir offSlabDir offBktMeta offFpHash
      offBktHash; omega⟩) _ _

/-- Wrapper around `GoodEpochAt.initZeroed` without requiring `s.mem fl.metaBase = fl.N` before
`epochInitZeroedProg` (which writes `fl.metaBase := fl.N` as its first step). -/
theorem GoodEpochAt.of_initZeroed {fl : FastEpochLayout} {w slack : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {s : Memory.State}
    (hv : fl.Valid w s.frontier) (hpt : fl.ParamTable s.mem)
    (hbkt_rep : BitPackedDoubleTabulation.SeedRep fl.bktHashBase fl.w
      (redWidthWhp fl.U) (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (bWhp fl.N)
      seeds.bkt s.mem)
    (hfp_rep : BitPackedDoubleTabulation.SeedRep fl.fpHashBase fl.w
      (redWidthWhp fl.U) (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (fpBitsWhp fl.N)
      seeds.fp s.mem)
    (hzero_hdr : ∀ k, 1 ≤ k → k < 32 → s.mem (fl.metaBase + k) = 0)
    (hzero_tab : ∀ addr, fl.metaBase + offBktMeta fl.c fl.w fl.N ≤ addr →
      addr < fl.metaBase + offPageDir fl.c fl.w fl.N → s.mem addr = 0)
    (hio : fl.io.StateInv 0 slack s.mem) :
    GoodEpochAt fl slack seeds []
      ((Memory.spec 0).clientState s (epochInitZeroedProg fl.pBase)).mem := by
  have hN_pos : 0 < fl.N := lt_of_lt_of_le (whpThreshold_pos fl.c) hv.thresh_le
  have hm0 : s.mem fl.pBase = fl.N := hpt 0 (by decide)
  have hm1 : s.mem (fl.pBase + 1) = fl.metaBase := hpt 1 (by decide)
  set s1 : Memory.State := { mem := Function.update s.mem fl.metaBase fl.N, frontier := s.frontier }
  have hpt1 : fl.ParamTable s1.mem := hpt.congr fun a h1 _ =>
    Function.update_of_ne (by have := hv.pBase_lt_meta; omega) _ _
  have hw_pos : 0 < fl.w := hv.w_eq ▸ hv.w_pos
  have hbkt1 : BitPackedDoubleTabulation.SeedRep fl.bktHashBase fl.w
      (redWidthWhp fl.U) (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (bWhp fl.N)
      seeds.bkt s1.mem :=
    hbkt_rep.congr_on hw_pos fun a h1 _ => by
      have hne : a ≠ fl.metaBase := by
        unfold FastEpochLayout.bktHashBase offBktHash at h1; omega
      simp [s1, hne]
  have hfp1 : BitPackedDoubleTabulation.SeedRep fl.fpHashBase fl.w
      (redWidthWhp fl.U) (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (fpBitsWhp fl.N)
      seeds.fp s1.mem :=
    hfp_rep.congr_on hw_pos fun a h1 _ => by
      have hne : a ≠ fl.metaBase := by
        unfold FastEpochLayout.fpHashBase offFpHash offBktHash at h1; omega
      simp [s1, hne]
  have hzh1 : ∀ k, 1 ≤ k → k < 32 → s1.mem (fl.metaBase + k) = 0 := fun k hk1 hk2 => by
    dsimp only [s1]; rw [Function.update_of_ne (by omega)]; exact hzero_hdr k hk1 hk2
  have hzt1 : ∀ addr, fl.metaBase + offBktMeta fl.c fl.w fl.N ≤ addr →
      addr < fl.metaBase + offPageDir fl.c fl.w fl.N → s1.mem addr = 0 := fun a h1 h2 => by
    have h32 : 32 ≤ offBktMeta fl.c fl.w fl.N := hv.mp_valid.offBktMeta_ge
    dsimp only [s1]; rw [Function.update_of_ne (by omega)]; exact hzero_tab a h1 h2
  have hio1 : fl.io.StateInv 0 slack s1.mem :=
    (fl.io.congr_of_outside hv.io_valid.w_pos hio fun a ha =>
      Function.update_of_ne (fun he =>
        hv.disj_fast_io a (Or.inl ⟨by rw [he], by rw [he]; omega⟩) ha) _ _).1
  have hst_eq : (Memory.spec 0).clientState s (epochInitZeroedProg fl.pBase) =
      (Memory.spec 0).clientState s1 (epochInitZeroedProg fl.pBase) := by
    unfold epochInitZeroedProg
    have hp0_1 : s1.mem fl.pBase = fl.N := hpt1 0 (by decide)
    have hp1_1 : s1.mem (fl.pBase + 1) = fl.metaBase := hpt1 1 (by decide)
    rw [StateTransitionSpec.clientState_bind, cstate_rd, cres_rd, hm0,
      StateTransitionSpec.clientState_bind, cstate_rd, cres_rd, hm1,
      ite_eq_right hN_pos.ne', StateTransitionSpec.clientState_bind, cstate_wr,
      StateTransitionSpec.clientState_bind, cstate_rd, cres_rd, hp0_1,
      StateTransitionSpec.clientState_bind, cstate_rd, cres_rd, hp1_1,
      ite_eq_right hN_pos.ne', StateTransitionSpec.clientState_bind, cstate_wr]
    have hidem : Function.update s1.mem fl.metaBase fl.N = s1.mem := by
      funext x; dsimp only [s1]
      by_cases hx : x = fl.metaBase
      · subst hx; simp
      · simp [Function.update_of_ne hx]
    rw [hidem]
  rw [hst_eq]
  exact GoodEpochAt.initZeroed hv hpt1 (Function.update_self ..) hbkt1 hfp1 hzh1 hzt1 hio1

/-! ## Section 3: Canonical Layouts, `SlotLatent`, and Uniform `EpochSlotInv` API -/

/-- Canonical direct (`usePaged = 0, sideBit = 0`) `SlotIoLayout` matching `setDirectSlotIoProg`. -/
@[expose] def directSlotIo (w vBits base ib qb nc : ℕ) : SlotIoLayout :=
  ⟨0, 0, ⟨base + hdrSplit, ib, qb, 1, w, 32, 4, ib, qb, vBits, nc⟩⟩

/-- Canonical `SplitPair` (`usePaged = 0, sideBit = 1`) `SlotIoLayout` matching
`setSplitSlotIoProg`. -/
@[expose] def splitSlotIo (w vBits base ibLo qLo ibHi qHi nc : ℕ) : SlotIoLayout :=
  ⟨0, 1, ⟨base + hdrSplit, ibLo, qHi, 1, w, 32, 4, ibHi, qLo, vBits, nc⟩⟩

/-- Canonical paged (`usePaged = 1`) `SlotIoLayout` on side `sb ∈ {0, 1}` of `pgL`. -/
@[expose] def pagedSlotIo (sb : ℕ) (pgL : PageArenaLayout) : SlotIoLayout :=
  ⟨1, sb, pgL⟩

/-- Canonical `PageArenaLayout` hosted in epoch `(nHost, mbHost)`. -/
@[expose] def hostPageLayout (c w nHost mbHost ibHi qHi vBits nc : ℕ) : PageArenaLayout :=
  epochPageArenaLayout c w nHost mbHost ibHi qHi vBits nc

/-- Replace `io.pgL.nCap` by `nc'`. -/
@[expose] def SlotIoLayout.withNCap (io : SlotIoLayout) (nc' : ℕ) : SlotIoLayout :=
  { io with pgL := { io.pgL with nCap := nc' } }

/-- Non-dependent latent logical and probabilistic state of one epoch slot. -/
structure SlotLatent (c U V : ℕ) where
  /-- Epoch capacity (`0` = small unhashed regime, `whpThreshold c ≤ nCap` = large hashed). -/
  nCap : ℕ
  /-- Current abstract map stored in this slot. -/
  s_abs : Fin U → Option (Fin V)
  /-- Sampled epoch hash seeds (singleton when `nCap < whpThreshold c`). -/
  seeds : EpochHashSeeds c U nCap
  /-- Pre-drain chronological `EpochUpdate` log (frozen upon entering `draining = true`). -/
  evs : List (EpochUpdate U V)

/-- Empty small-regime `SlotLatent` (`nCap = 0`). -/
@[expose] noncomputable def SlotLatent.emptySmall (c U V : ℕ) : SlotLatent c U V where
  nCap := 0
  s_abs := fun _ => none
  seeds := Classical.choice inferInstance
  evs := []

/-- Good-seed event for `sl` over `windowOfEvents` (vacuously `True` when `sl.nCap = 0`). -/
@[expose] def SlotLatent.Good {c U V : ℕ} (sl : SlotLatent c U V) : Prop :=
  ∀ (hth : whpThreshold c ≤ sl.nCap) (hlen : sl.evs.length ≤ 4 * sl.nCap)
    (hcard : ∀ k ≤ sl.evs.length, (liveDom (EpochUpdate.eval (sl.evs.take k))).card ≤ sl.nCap),
    GoodEpochSeeds (windowOfEvents hth sl.evs hlen hcard) sl.seeds

/-- Prefix-monotone good-window coverage for `sl` (`True` when `sl.nCap = 0`, preserved backward
under `evs ↦ evs ++ extra` via `SlotLatent.GoodCovers.of_append`). -/
@[expose] def SlotLatent.GoodCovers {c U V : ℕ} (sl : SlotLatent c U V) : Prop :=
  ∀ (_hth : whpThreshold c ≤ sl.nCap),
    ∃ (win : EpochWindowSpec c U sl.nCap),
      GoodEpochSeeds win sl.seeds ∧ WindowCovers sl.evs win

theorem SlotLatent.good_of_small {c U V : ℕ} {sl : SlotLatent c U V} (h0 : sl.nCap = 0) :
    sl.Good := fun hth => absurd (h0 ▸ hth) (Nat.not_le_of_gt (whpThreshold_pos c))

theorem SlotLatent.goodCovers_of_small {c U V : ℕ} {sl : SlotLatent c U V} (h0 : sl.nCap = 0) :
    sl.GoodCovers := fun hth => absurd (h0 ▸ hth) (Nat.not_le_of_gt (whpThreshold_pos c))

theorem SlotLatent.GoodCovers.of_append {c U V nCap : ℕ}
    {s₁ s₂ : Fin U → Option (Fin V)} {seeds : EpochHashSeeds c U nCap}
    {evs extra : List (EpochUpdate U V)}
    (h : (⟨nCap, s₂, seeds, evs ++ extra⟩ : SlotLatent c U V).GoodCovers) :
    (⟨nCap, s₁, seeds, evs⟩ : SlotLatent c U V).GoodCovers := fun hth => by
  obtain ⟨win, hgood, hcov⟩ := h hth
  exact ⟨win, hgood, hcov.of_append⟩

theorem SlotLatent.GoodCovers.congr_abs {c U V : ℕ} {sl : SlotLatent c U V}
    (s' : Fin U → Option (Fin V)) (h : sl.GoodCovers) :
    ({ sl with s_abs := s' } : SlotLatent c U V).GoodCovers := h

/-- Unified epoch-slot invariant covering `sl.nCap = 0` (`SmallEpochLayout`) and `0 < sl.nCap`
(`FastEpochLayout` + `LargeEpochInv`, with `GoodEpochAt` when `draining = false` and latched
`sl.GoodCovers → mode = 0` when `draining = true` in Phase `8`). -/
@[expose] def EpochSlotInv (c U V w fr pBase metaBase : ℕ) (io : SlotIoLayout)
    (slack : ℕ) (draining : Bool) (sl : SlotLatent c U V) (mem : ℕ → ℕ) : Prop :=
  if sl.nCap = 0 then
    let L : SmallEpochLayout := ⟨metaBase, U, V, io⟩
    6 ≤ w ∧ pBase + 64 ≤ fr ∧ L.Valid w fr ∧ L.ParamTable pBase mem ∧
    (∀ a, pBase ≤ a → a < pBase + 64 → ¬L.OwnsAddr a) ∧
    L.StateInv slack mem sl.s_abs
  else
    let fl : FastEpochLayout := ⟨c, U, V, w, sl.nCap, metaBase, pBase, io⟩
    fl.Valid w fr ∧
    LargeEpochInv fl slack sl.seeds mem sl.s_abs ∧
    mem fl.fpHashBase < 2 ^ (redWidthWhp U - 1) ∧
    (∀ k ≤ sl.evs.length, (liveDom (EpochUpdate.eval (sl.evs.take k))).card ≤ sl.nCap) ∧
    if draining then
      sl.GoodCovers → mem (fl.metaBase + 2) = 0
    else
      EpochUpdate.eval sl.evs = sl.s_abs ∧
      GoodEpochAt fl slack sl.seeds sl.evs mem

/-- Footprint mutable by operations on an `EpochSlotInv` slot. -/
@[expose] def slotOwnsAddr (c w metaBase nCap : ℕ) (io : SlotIoLayout) (addr : ℕ) : Prop :=
  if nCap = 0 then
    (⟨metaBase, 0, 0, io⟩ : SmallEpochLayout).OwnsAddr addr
  else
    (⟨c, 0, 0, w, nCap, metaBase, 0, io⟩ : FastEpochLayout).OwnsFastAddr addr

theorem EpochSlotInv.fastLayoutReady {c U V w pBase metaBase slack : ℕ} {io : SlotIoLayout}
    {draining : Bool} {sl : SlotLatent c U V} {s : Memory.State}
    (h : EpochSlotInv c U V w s.frontier pBase metaBase io slack draining sl s.mem)
    (hne : sl.nCap ≠ 0) :
    FastLayoutReady w ⟨c, U, V, w, sl.nCap, metaBase, pBase, io⟩ s := by
  unfold EpochSlotInv at h; rw [ite_eq_right hne] at h
  rcases h.2.1.2 with ⟨_, hf⟩ | ⟨_, hfb⟩
  · exact hf.ready h.1 rfl
  · exact fastLayoutReady_of_fallback rfl h.1 h.2.1.1 hfb h.2.2.1

theorem EpochSlotInv.epochProgPre {c U V w pBase metaBase slack : ℕ} {io : SlotIoLayout}
    {draining : Bool} {sl : SlotLatent c U V} {s : Memory.State}
    (h : EpochSlotInv c U V w s.frontier pBase metaBase io slack draining sl s.mem) :
    EpochProgPre w pBase s := by
  by_cases h0 : sl.nCap = 0
  · unfold EpochSlotInv at h; rw [ite_eq_left h0] at h
    exact EpochProgPre.of_small ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  · exact EpochProgPre.of_large (h.fastLayoutReady h0)

theorem EpochSlotInv.epochInsertProgPre {c U V w pBase metaBase slack : ℕ}
    {io : SlotIoLayout} {draining : Bool} {sl : SlotLatent c U V} {s : Memory.State}
    (h : EpochSlotInv c U V w s.frontier pBase metaBase io slack draining sl s.mem) :
    EpochInsertProgPre w pBase s := by
  unfold EpochSlotInv at h
  by_cases h0 : sl.nCap = 0
  · rw [ite_eq_left h0] at h
    exact EpochInsertProgPre.of_small ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  · rw [ite_eq_right h0] at h
    exact EpochInsertProgPre.of_large h.1 h.2.1 h.2.2.1

theorem EpochSlotInv.mem_nSide_eq {c U V w fr pBase metaBase slack : ℕ}
    {io : SlotIoLayout} {draining : Bool} {sl : SlotLatent c U V} {mem : ℕ → ℕ}
    (h : EpochSlotInv c U V w fr pBase metaBase io slack draining sl mem) :
    mem (metaBase + 1) = (liveDom sl.s_abs).card := by
  classical
  unfold EpochSlotInv at h
  by_cases h0 : sl.nCap = 0
  · rw [ite_eq_left h0] at h; exact h.2.2.2.2.2.nSide_eq_card
  · rw [ite_eq_right h0] at h
    rcases h.2.1.2 with ⟨_, hf⟩ | ⟨_, hfb⟩
    · exact (hf.toGen 0).nSide_eq_card
    · dsimp only [FastEpochLayout.fbL] at hfb
      refine hfb.nSide_eq_card.trans (congrArg Finset.card (Finset.ext fun u => ?_))
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_liveDom_iff]

theorem EpochSlotInv.readNSide_eq {c U V w pBase metaBase slack : ℕ}
    {io : SlotIoLayout} {draining : Bool} {sl : SlotLatent c U V} {s : Memory.State}
    (h : EpochSlotInv c U V w s.frontier pBase metaBase io slack draining sl s.mem) :
    (Memory.spec 0).clientResult s (epochReadNSideProg pBase) = (liveDom sl.s_abs).card := by
  have hm := h.mem_nSide_eq
  unfold EpochSlotInv at h
  by_cases h0 : sl.nCap = 0
  · rw [ite_eq_left h0] at h
    exact (clientResult_epochReadNSideProg_small h.2.2.2.1).trans hm
  · rw [ite_eq_right h0] at h
    exact (clientResult_epochReadNSideProg_large h.2.1.1).trans hm

theorem EpochSlotInv.io_stateInv {c U V w fr pBase metaBase slack : ℕ}
    {io : SlotIoLayout} {draining : Bool} {sl : SlotLatent c U V} {mem : ℕ → ℕ}
    (h : EpochSlotInv c U V w fr pBase metaBase io slack draining sl mem) :
    io.StateInv (mem (metaBase + 1)) slack mem := by
  unfold EpochSlotInv at h
  by_cases h0 : sl.nCap = 0
  · rw [ite_eq_left h0] at h; exact h.2.2.2.2.2.2.2.1
  · rw [ite_eq_right h0] at h
    rcases h.2.1.2 with ⟨_, hf⟩ | ⟨_, hfb⟩
    · exact hf.bp_inv.2.2
    · exact hfb.io_inv

theorem EpochSlotInv.io_valid {c U V w fr pBase metaBase slack : ℕ}
    {io : SlotIoLayout} {draining : Bool} {sl : SlotLatent c U V} {mem : ℕ → ℕ}
    (h : EpochSlotInv c U V w fr pBase metaBase io slack draining sl mem) :
    io.Valid w fr := by
  unfold EpochSlotInv at h
  by_cases h0 : sl.nCap = 0
  · rw [ite_eq_left h0] at h; exact h.2.2.1.io_valid
  · rw [ite_eq_right h0] at h; exact h.1.io_valid

theorem EpochSlotInv.goodCovers_of_good {c U V w fr pBase metaBase slack : ℕ}
    {io : SlotIoLayout} {draining : Bool} {sl : SlotLatent c U V} {mem : ℕ → ℕ}
    (h : EpochSlotInv c U V w fr pBase metaBase io slack draining sl mem)
    (hlen : sl.nCap ≠ 0 → sl.evs.length ≤ 4 * sl.nCap) (hg : sl.Good) :
    sl.GoodCovers := fun hth => by
  have hne : sl.nCap ≠ 0 := (lt_of_lt_of_le (whpThreshold_pos c) hth).ne'
  unfold EpochSlotInv at h; rw [ite_eq_right hne] at h
  exact ⟨windowOfEvents hth sl.evs (hlen hne) h.2.2.2.1,
    hg hth (hlen hne) h.2.2.2.1, windowCovers_windowOfEvents hth sl.evs (hlen hne) h.2.2.2.1⟩

theorem EpochSlotInv.mode_zero_of_goodCovers {c U V w fr pBase metaBase slack : ℕ}
    {io : SlotIoLayout} {draining : Bool} {sl : SlotLatent c U V} {mem : ℕ → ℕ}
    (h : EpochSlotInv c U V w fr pBase metaBase io slack draining sl mem)
    (hne : sl.nCap ≠ 0) (hgc : sl.GoodCovers) :
    mem (metaBase + 2) = 0 := by
  unfold EpochSlotInv at h; rw [ite_eq_right hne] at h
  obtain ⟨hv, _, _, _, hgd⟩ := h
  cases draining
  · obtain ⟨win, hgood, hcov⟩ := hgc hv.thresh_le
    exact (hgd.2 win hgood hcov).1
  · exact hgd hgc

/-- Latch `GoodEpochAt` into `draining = true` when entering Phase `8` (`migrate`). -/
theorem EpochSlotInv.enter_draining {c U V w fr pBase metaBase slack : ℕ}
    {io : SlotIoLayout} {sl : SlotLatent c U V} {mem : ℕ → ℕ}
    (h : EpochSlotInv c U V w fr pBase metaBase io slack false sl mem) :
    EpochSlotInv c U V w fr pBase metaBase io slack true sl mem := by
  unfold EpochSlotInv at h ⊢
  by_cases h0 : sl.nCap = 0
  · rw [ite_eq_left h0] at h ⊢; exact h
  · rw [ite_eq_right h0] at h ⊢
    obtain ⟨hv, hinv, hfp, hcd, _, hgd⟩ := h
    refine ⟨hv, hinv, hfp, hcd, fun hgc => ?_⟩
    obtain ⟨win, hgood, hcov⟩ := hgc hv.thresh_le
    exact (hgd win hgood hcov).1

/-- Monotonicity of `EpochSlotInv` when `frontier` increases (`fr₁ ≤ fr₂`). -/
theorem EpochSlotInv.mono_frontier {c U V w fr₁ fr₂ pBase metaBase slack : ℕ}
    {io : SlotIoLayout} {draining : Bool} {sl : SlotLatent c U V} {mem : ℕ → ℕ}
    (h : EpochSlotInv c U V w fr₁ pBase metaBase io slack draining sl mem) (hle : fr₁ ≤ fr₂) :
    EpochSlotInv c U V w fr₂ pBase metaBase io slack draining sl mem := by
  have hio_mono : io.Valid w fr₁ → io.Valid w fr₂ := fun hv => by
    unfold SlotIoLayout.Valid at hv ⊢
    by_cases hup : io.usePaged = 0
    · rw [ite_eq_left hup] at hv ⊢
      refine ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2.1, ?_⟩
      have hs := hv.2.2.2.2.2
      split_ifs at hs ⊢
      · exact hs.trans hle
      · exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.trans hle⟩
    · rw [ite_eq_right hup] at hv ⊢
      unfold PageArenaLayout.Valid at hv ⊢
      exact ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2.1, hv.2.2.2.2.2.1,
        hv.2.2.2.2.2.2.1, hv.2.2.2.2.2.2.2.1, hv.2.2.2.2.2.2.2.2.1, hv.2.2.2.2.2.2.2.2.2.1,
        hv.2.2.2.2.2.2.2.2.2.2.1, hv.2.2.2.2.2.2.2.2.2.2.2.1,
        hv.2.2.2.2.2.2.2.2.2.2.2.2.1, hv.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
        hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.trans hle⟩
  unfold EpochSlotInv at h ⊢
  by_cases h0 : sl.nCap = 0
  · rw [ite_eq_left h0] at h ⊢
    obtain ⟨hw6, hp, hv, hpt, hdisj, hst⟩ := h
    exact ⟨hw6, hp.trans hle, ⟨hio_mono hv.io_valid, hv.w_eq, hv.qBits_eq, hv.vBits_eq,
      hv.hdr_frontier.trans hle, hv.disjoint_hdr⟩, hpt, hdisj, hst⟩
  · rw [ite_eq_right h0] at h ⊢
    obtain ⟨hv, hinv, hfp, hcd, hgd⟩ := h
    exact ⟨{ hv with
        meta_frontier := hv.meta_frontier.trans hle
        io_valid := hio_mono hv.io_valid }, hinv, hfp, hcd, hgd⟩

/-- Non-page metadata word-interval predicate for a small (`nCap = 0`) or large (`nCap ≠ 0`)
epoch slot (excluding `PageUnpermState` scalars `[metaBase + 18, metaBase + 32)`). -/
@[expose] def slotOwnsNonPageMeta (c w metaBase nCap addr : ℕ) : Prop :=
  (metaBase ≤ addr ∧ addr < metaBase + (if nCap = 0 then 2 else 18)) ∨
  (nCap ≠ 0 ∧ metaBase + 32 ≤ addr ∧ addr < metaBase + offPageDir c w nCap)

/-- Transport `EpochSlotInv` across a `SlotIoLayout` / `slack` switch (`io ↦ io₂`, `slack₁ ↦
slack₂`). -/
theorem EpochSlotInv.transfer_io {c U V w fr pBase metaBase slack₁ slack₂ : ℕ}
    {io io₂ : SlotIoLayout} {draining : Bool} {sl : SlotLatent c U V} {mem₁ mem₂ : ℕ → ℕ}
    (h : EpochSlotInv c U V w fr pBase metaBase io slack₁ draining sl mem₁)
    (hv_io₂ : io₂.Valid w fr)
    (hw_io₂ : io₂.pgL.w = w)
    (hq_io₂ : (sl.nCap = 0 → io₂.pgL.qBits = keyBits U) ∧
      (sl.nCap ≠ 0 → quotBitsWhp U sl.nCap ≤ io₂.pgL.qBits))
    (hvb_io₂ : io₂.pgL.vBits = valBits V)
    (hpt₂ :
      (sl.nCap = 0 →
        ({ metaBase := metaBase, U := U, V := V, io := io₂ } : SmallEpochLayout).ParamTable
          pBase mem₂) ∧
      (sl.nCap ≠ 0 →
        ({ c := c, U := U, V := V, w := w, N := sl.nCap, metaBase := metaBase, pBase := pBase,
           io := io₂ } : FastEpochLayout).ParamTable mem₂))
    (hdisj_p₂ : ∀ a, pBase ≤ a → a < pBase + 64 → ¬io₂.OwnsAddr a)
    (hdisj_m₂ : ∀ a, slotOwnsNonPageMeta c w metaBase sl.nCap a → ¬io₂.OwnsAddr a)
    (hm : ∀ a, slotOwnsNonPageMeta c w metaBase sl.nCap a → mem₂ a = mem₁ a)
    (hio₂ : io₂.StateInv (mem₁ (metaBase + 1)) slack₂ mem₂)
    (hpair : ∀ p < mem₁ (metaBase + 1), slotIoPairAt io₂ mem₂ p = slotIoPairAt io mem₁ p) :
    EpochSlotInv c U V w fr pBase metaBase io₂ slack₂ draining sl mem₂ := by
  have hio_old := h.io_stateInv
  unfold EpochSlotInv at h ⊢
  by_cases h0 : sl.nCap = 0
  · rw [ite_eq_left h0] at h ⊢
    obtain ⟨hw6, hp_fr, hv, _, hdisj₁, hst⟩ := h
    let L₂ : SmallEpochLayout := ⟨metaBase, U, V, io₂⟩
    have hv₂ : L₂.Valid w fr :=
      { io_valid := hv_io₂
        w_eq := hw_io₂.symm
        qBits_eq := hq_io₂.1 h0
        vBits_eq := hvb_io₂
        hdr_frontier := hv.hdr_frontier
        disjoint_hdr := fun addr hmb hia =>
          hdisj_m₂ addr (Or.inl (by
            dsimp only [L₂] at hmb
            simp only [h0, ↓reduceIte]
            rcases hmb with rfl | rfl <;> omega)) hia }
    have hm0 : mem₂ metaBase = mem₁ metaBase :=
      hm _ (Or.inl ⟨le_rfl, by simp only [h0, ↓reduceIte]; omega⟩)
    have hm1 : mem₂ (metaBase + 1) = mem₁ (metaBase + 1) :=
      hm _ (Or.inl ⟨by omega, by simp only [h0, ↓reduceIte]; omega⟩)
    have hdisj₂ : ∀ a, pBase ≤ a → a < pBase + 64 → ¬L₂.OwnsAddr a := fun a h1 h2 ha => by
      rcases ha with rfl | rfl | hia
      · exact hdisj₁ _ h1 h2 (Or.inl rfl)
      · exact hdisj₁ _ h1 h2 (Or.inr (Or.inl rfl))
      · exact hdisj_p₂ a h1 h2 hia
    have hst₂ : L₂.StateInv slack₂ mem₂ sl.s_abs := by
      have hnc₂ : mem₁ (metaBase + 1) ≤ io₂.pgL.nCap := by
        have hi := hio₂; unfold SlotIoLayout.StateInv at hi
        by_cases hup : io₂.usePaged = 0
        · rw [ite_eq_left hup] at hi; exact hi.1
        · rw [ite_eq_right hup] at hi
          have hvl := hi.2.2.2.2.1; have hti := hi.2.2.2.1
          unfold PagePairState.totalItems at hti
          cases hs : io₂.side <;> rw [hs] at hvl <;> omega
      exact SmallEpochLayout.StateInv.transfer_io hst hm0 hm1 hio₂ hnc₂ hpair
    exact ⟨hw6, hp_fr, hv₂, hpt₂.1 h0, hdisj₂, hst₂⟩
  · rw [ite_eq_right h0] at h ⊢
    obtain ⟨hv, hinv, hfp, hcd, hgd⟩ := h
    let fl : FastEpochLayout := ⟨c, U, V, w, sl.nCap, metaBase, pBase, io⟩
    let fl₂ : FastEpochLayout := { fl with io := io₂ }
    have hm_lg : ∀ a, OwnsEpochNonPageMeta c w sl.nCap metaBase a → mem₂ a = mem₁ a := fun a ha =>
      hm a (by
        rcases ha with h1 | h2
        · exact Or.inl ⟨h1.1, by simp only [h0, ↓reduceIte]; exact h1.2⟩
        · exact Or.inr ⟨h0, h2⟩)
    have hv₂ : fl₂.Valid w fr :=
      { hv with
        io_valid := hv_io₂
        w_eq_io := hw_io₂.symm
        qBits_le := hq_io₂.2 h0
        vBits_eq := hvb_io₂
        disj_pBase_io := hdisj_p₂
        disj_fast_io := fun addr ha => hdisj_m₂ addr (by
          rcases ha with h1 | h2
          · exact Or.inl ⟨h1.1, by simp only [h0, ↓reduceIte]; exact h1.2⟩
          · exact Or.inr ⟨h0, h2⟩) }
    have hinv₂ : LargeEpochInv fl₂ slack₂ sl.seeds mem₂ sl.s_abs :=
      hinv.transfer_io hv (hpt₂.2 h0) hm_lg (fun _ => hio₂) (fun _ => hio₂)
        (fun p hp_lt => hpair p (by split_ifs at hp_lt <;> exact hp_lt))
    have hsp_fp := BitPackedDoubleTabulation.space_pos w (cTabWhp c) (dTabWhp c)
      (bCharWhp sl.nCap) (fpBitsWhp sl.nCap)
    have hfp_eq : mem₂ fl₂.fpHashBase = mem₁ fl.fpHashBase := hm_lg _ (Or.inr
      ⟨by dsimp only [FastEpochLayout.fpHashBase, fl₂, fl]; unfold offFpHash offBktHash; omega,
       by dsimp only [FastEpochLayout.fpHashBase, fl₂, fl]
          unfold offPageDir offTrieItem offTrieNode offTrieChild offBTreeVals offBTreeKeys
            offBTreeMeta offTailOwner offSlabOwner offTailDir offSlabDir offBktMeta offFpHash
            offBktHash; omega⟩)
    have hm2_eq : mem₂ (metaBase + 2) = mem₁ (metaBase + 2) :=
      hm_lg _ (Or.inl ⟨by omega, by omega⟩)
    refine ⟨hv₂, hinv₂, hfp_eq ▸ hfp, hcd, ?_⟩
    cases draining
    · exact ⟨hgd.1, hgd.2.transfer_io hv (hpt₂.2 h0) hm_lg (fun _ => hio₂) (fun _ => hpair)⟩
    · exact fun hgc => hm2_eq.trans (hgd hgc)

/-- Frame congruence for `EpochSlotInv` when `[pBase, pBase + 64)`, non-page metadata, and
`io.OwnsAddr` are preserved. -/
theorem EpochSlotInv.congr_mem {c U V w fr pBase metaBase slack : ℕ}
    {io : SlotIoLayout} {draining : Bool} {sl : SlotLatent c U V} {mem₁ mem₂ : ℕ → ℕ}
    (h : EpochSlotInv c U V w fr pBase metaBase io slack draining sl mem₁)
    (hp : ∀ a, pBase ≤ a → a < pBase + 64 → mem₂ a = mem₁ a)
    (hm : ∀ a, slotOwnsNonPageMeta c w metaBase sl.nCap a → mem₂ a = mem₁ a)
    (hio : ∀ a, io.OwnsAddr a → mem₂ a = mem₁ a) :
    EpochSlotInv c U V w fr pBase metaBase io slack draining sl mem₂ := by
  have hv_io := h.io_valid
  obtain ⟨hio₂, hpair⟩ := io.congr_of_outside hv_io.w_pos h.io_stateInv hio
  have hraw := h; unfold EpochSlotInv at hraw
  refine h.transfer_io hv_io ?_ ⟨fun h0 => ?_, fun h0 => ?_⟩ ?_ ⟨fun h0 => ?_, fun h0 => ?_⟩
    (fun a h1 h2 => ?_) (fun a ha => ?_) hm hio₂ hpair
  · by_cases h0 : sl.nCap = 0
    · rw [ite_eq_left h0] at hraw; exact hraw.2.2.1.w_eq.symm
    · rw [ite_eq_right h0] at hraw; exact hraw.1.w_eq_io.symm
  · rw [ite_eq_left h0] at hraw; exact hraw.2.2.1.qBits_eq
  · rw [ite_eq_right h0] at hraw; exact hraw.1.qBits_le
  · by_cases h0 : sl.nCap = 0
    · rw [ite_eq_left h0] at hraw; exact hraw.2.2.1.vBits_eq
    · rw [ite_eq_right h0] at hraw; exact hraw.1.vBits_eq
  · rw [ite_eq_left h0] at hraw; exact hraw.2.2.2.1.congr hp
  · rw [ite_eq_right h0] at hraw
    exact hraw.2.1.1.congr fun a h1 h2 => hp a h1 (by dsimp only at h1 h2; omega)
  · by_cases h0 : sl.nCap = 0
    · rw [ite_eq_left h0] at hraw; exact fun hia => hraw.2.2.2.2.1 a h1 h2 (Or.inr (Or.inr hia))
    · rw [ite_eq_right h0] at hraw; exact hraw.1.disj_pBase_io a h1 h2
  · unfold slotOwnsNonPageMeta at ha
    by_cases h0 : sl.nCap = 0
    · rw [ite_eq_left h0] at hraw ha
      rcases ha with ⟨h1, h2⟩ | ⟨hne, _⟩
      · have hd := hraw.2.2.1.disjoint_hdr a
        dsimp only at hd
        exact hd (by omega)
      · exact absurd h0 hne
    · rw [ite_eq_right h0] at hraw ha
      exact hraw.1.disj_fast_io a (ha.imp id And.right)

/-- Updating `pBase + 60` (`io.pgL.nCap := nc'`) preserves `EpochSlotInv` at `io.withNCap nc'`. -/
theorem EpochSlotInv.update_nCap {c U V w fr pBase metaBase slack nc' : ℕ}
    {io : SlotIoLayout} {draining : Bool} {sl : SlotLatent c U V} {mem : ℕ → ℕ}
    (h : EpochSlotInv c U V w fr pBase metaBase io slack draining sl mem)
    (hv_io' : (io.withNCap nc').Valid w fr)
    (hdisj_p' : ∀ a, pBase ≤ a → a < pBase + 64 → ¬(io.withNCap nc').OwnsAddr a)
    (hdisj_m' : ∀ a, slotOwnsNonPageMeta c w metaBase sl.nCap a → ¬(io.withNCap nc').OwnsAddr a)
    (hdisj_pm : pBase + 64 ≤ metaBase ∨
      metaBase + (if sl.nCap = 0 then 2 else offPageDir c w sl.nCap) ≤ pBase)
    (hnc_ge : mem (metaBase + 1) ≤ nc')
    (hnc_pg : io.usePaged ≠ 0 → (extractPagePair io.pgL mem).totalItems ≤ nc') :
    EpochSlotInv c U V w fr pBase metaBase (io.withNCap nc') slack draining sl
      (Function.update mem (pBase + 60) nc') := by
  set mem' := Function.update mem (pBase + 60) nc'
  set io' := io.withNCap nc'
  have hdisj_io : ∀ a, pBase ≤ a → a < pBase + 64 → ¬io.OwnsAddr a := by
    have hr := h; unfold EpochSlotInv at hr
    by_cases h0 : sl.nCap = 0
    · rw [ite_eq_left h0] at hr; exact fun a h1 h2 hia => hr.2.2.2.2.1 a h1 h2 (Or.inr (Or.inr hia))
    · rw [ite_eq_right h0] at hr; exact hr.1.disj_pBase_io
  have hmem_io : ∀ a, io.OwnsAddr a → mem' a = mem a := fun a ha =>
    Function.update_of_ne (fun he => hdisj_io a (by omega) (by omega) ha) _ _
  obtain ⟨hio_m', harr⟩ := io.congr_of_outside hv_io'.w_pos h.io_stateInv hmem_io
  have hpair : ∀ p < mem (metaBase + 1), slotIoPairAt io' mem' p = slotIoPairAt io mem p := by
    intro p hp; exact harr p hp
  have hio'_inv : io'.StateInv (mem (metaBase + 1)) slack mem' := by
    unfold SlotIoLayout.StateInv at hio_m' ⊢
    by_cases hup : io.usePaged = 0
    · have hup' : io'.usePaged = 0 := hup
      rw [ite_eq_left hup] at hio_m'; rw [ite_eq_left hup']
      exact ⟨hnc_ge, hio_m'.2⟩
    · have hup' : io'.usePaged ≠ 0 := hup
      rw [ite_eq_right hup] at hio_m'; rw [ite_eq_right hup']
      have hu_eq : extractPageUnperm io.pgL mem' = extractPageUnperm io.pgL mem :=
        extractPageUnperm_congr hv_io'.w_pos fun a ha =>
          hmem_io a (by unfold SlotIoLayout.OwnsAddr; rw [ite_eq_right hup]; exact Or.inl ha)
      have hu_eq' : extractPageUnperm io'.pgL mem' = extractPageUnperm io.pgL mem := hu_eq
      rw [hu_eq']
      rw [hu_eq] at hio_m'
      exact ⟨hio_m'.1, hio_m'.2.1, hio_m'.2.2.1, hnc_pg hup, hio_m'.2.2.2.2⟩
  have hraw := h; unfold EpochSlotInv at hraw
  refine h.transfer_io hv_io' ?_ ⟨fun h0 => ?_, fun h0 => ?_⟩ ?_ ⟨fun h0 => ?_, fun h0 => ?_⟩
    hdisj_p' hdisj_m'
    (fun a ha => Function.update_of_ne (by
      unfold slotOwnsNonPageMeta at ha
      rcases ha with ⟨h1, h2⟩ | ⟨hne, h1, h2⟩ <;> rcases hdisj_pm with hpm | hmp
      · omega
      · by_cases hc0 : sl.nCap = 0
        · rw [ite_eq_left hc0] at h2 hmp; omega
        · rw [ite_eq_right hc0] at h2 hmp
          have hod : 32 ≤ offPageDir c w sl.nCap := by
            unfold offPageDir offTrieItem offTrieNode offTrieChild offBTreeVals offBTreeKeys
              offBTreeMeta offTailOwner offSlabOwner offTailDir offSlabDir offBktMeta offFpHash
              offBktHash
            omega
          omega
      · omega
      · rw [ite_eq_right hne] at hmp; omega) _ _)
    hio'_inv hpair
  · by_cases h0 : sl.nCap = 0
    · rw [ite_eq_left h0] at hraw; exact hraw.2.2.1.w_eq.symm
    · rw [ite_eq_right h0] at hraw; exact hraw.1.w_eq_io.symm
  · rw [ite_eq_left h0] at hraw; exact hraw.2.2.1.qBits_eq
  · rw [ite_eq_right h0] at hraw; exact hraw.1.qBits_le
  · by_cases h0 : sl.nCap = 0
    · rw [ite_eq_left h0] at hraw; exact hraw.2.2.1.vBits_eq
    · rw [ite_eq_right h0] at hraw; exact hraw.1.vBits_eq
  · rw [ite_eq_left h0] at hraw
    have hpt0 := hraw.2.2.2.1
    unfold SmallEpochLayout.ParamTable at hpt0 ⊢
    have hne : ∀ k < 60, mem' (pBase + k) = mem (pBase + k) := fun k hk =>
      Function.update_of_ne (by omega) _ _
    exact ⟨(hne 0 (by decide)).trans hpt0.1, (hne 1 (by decide)).trans hpt0.2.1,
      (hne 48 (by decide)).trans hpt0.2.2.1, (hne 49 (by decide)).trans hpt0.2.2.2.1,
      (hne 50 (by decide)).trans hpt0.2.2.2.2.1, (hne 51 (by decide)).trans hpt0.2.2.2.2.2.1,
      (hne 52 (by decide)).trans hpt0.2.2.2.2.2.2.1,
      (hne 53 (by decide)).trans hpt0.2.2.2.2.2.2.2.1,
      (hne 54 (by decide)).trans hpt0.2.2.2.2.2.2.2.2.1,
      (hne 55 (by decide)).trans hpt0.2.2.2.2.2.2.2.2.2.1,
      (hne 56 (by decide)).trans hpt0.2.2.2.2.2.2.2.2.2.2.1,
      (hne 57 (by decide)).trans hpt0.2.2.2.2.2.2.2.2.2.2.2.1,
      (hne 58 (by decide)).trans hpt0.2.2.2.2.2.2.2.2.2.2.2.2.1,
      (hne 59 (by decide)).trans hpt0.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      Function.update_self ..⟩
  · rw [ite_eq_right h0] at hraw
    have hpt0 := hraw.2.1.1
    let fl₀ : FastEpochLayout := ⟨c, U, V, w, sl.nCap, metaBase, pBase, io⟩
    let fl₁ : FastEpochLayout := ⟨c, U, V, w, sl.nCap, metaBase, pBase, io'⟩
    change fl₁.ParamTable mem'
    intro k hk
    dsimp only [fl₁, mem']
    by_cases hk60 : k = 60
    · subst hk60; exact Function.update_self ..
    · rw [Function.update_of_ne (by omega : pBase + k ≠ pBase + 60)]
      have hpw : fl₁.paramWord k = fl₀.paramWord k := by
        interval_cases k <;> first | rfl | exact absurd rfl hk60
      exact (hpt0 k hk).trans hpw.symm

/-- Uniform specification of `epochQueryProg` on an `EpochSlotInv` slot. -/
theorem EpochSlotInv.query_spec {c U V w pBase metaBase slack : ℕ} {io : SlotIoLayout}
    {draining : Bool} {sl : SlotLatent c U V} {s : Memory.State}
    (h : EpochSlotInv c U V w s.frontier pBase metaBase io slack draining sl s.mem)
    (u : Fin U) :
    (Memory.spec 0).clientState s (epochQueryProg (pBase, u.val)) = s ∧
    (Memory.spec 0).clientResult s (epochQueryProg (pBase, u.val)) =
      (match sl.s_abs u with | none => (0, 0) | some v => (1, v.val)) ∧
    ((sl.nCap = 0 → (liveDom sl.s_abs).card ≤ 2 * whpThreshold c) →
      sl.GoodCovers →
      memoryCost (epochQueryProg (pBase, u.val)) s ≤ epochStepCost c) := by
  have hm_ns := h.mem_nSide_eq
  have hm2 : sl.nCap ≠ 0 → sl.GoodCovers → s.mem (metaBase + 2) = 0 :=
    fun hne => h.mode_zero_of_goodCovers hne
  unfold EpochSlotInv at h
  by_cases h0 : sl.nCap = 0
  · rw [ite_eq_left h0] at h
    obtain ⟨_, _, hv, hpt, _, hst⟩ := h
    obtain ⟨hst_q, hc_q, hres_q⟩ := epochQueryProg_spec_small hv hpt hst u
    refine ⟨hst_q, ?_, fun hsm _ => ?_⟩
    · cases hs : sl.s_abs u <;> simp only [hs] at hres_q ⊢ <;> exact hres_q
    · have hc1 := hsm h0
      dsimp only at hc_q
      rw [hm_ns] at hc_q
      unfold epochStepCost smallStepCost
      have hle := le_max_left (21 * (2 * whpThreshold c) + 1600) (largeFastStepCost c)
      omega
  · rw [ite_eq_right h0] at h
    obtain ⟨hv, hinv, _, _, _⟩ := h
    obtain ⟨hst_q, hres_q, hc_q⟩ := epochQueryProg_spec_large hv hinv u
    refine ⟨hst_q, ?_, fun _ hgc => hc_q (hm2 h0 hgc)⟩
    cases hs : sl.s_abs u <;> simp only [hs] at hres_q ⊢ <;> exact hres_q

/-- Uniform specification of `epochInsertProg` on an active (`draining = false`) `EpochSlotInv`
slot. -/
theorem EpochSlotInv.insert_spec {c U V w pBase metaBase : ℕ} {io : SlotIoLayout}
    {sl : SlotLatent c U V} {s : Memory.State}
    (h : EpochSlotInv c U V w s.frontier pBase metaBase io 0 false sl s.mem)
    (u : Fin U) (v : Fin V)
    (hcap_n : sl.s_abs u = none → sl.nCap ≠ 0 → (liveDom sl.s_abs).card < sl.nCap)
    (hcap_io : sl.s_abs u = none →
      (liveDom sl.s_abs).card < io.pgL.nCap ∧
      (io.usePaged ≠ 0 → (extractPagePair io.pgL s.mem).totalItems + 1 ≤ io.pgL.nCap)) :
    let s' := (Memory.spec 0).clientState s (epochInsertProg ((pBase, u.val), v.val))
    let slack' :=
      if io.usePaged = 0 ∨ (extractPageUnperm io.pgL s.mem).cleanPhase = 0 then 0 else 24
    let sl' : SlotLatent c U V :=
      ⟨sl.nCap, Function.update sl.s_abs u (some v), sl.seeds,
        sl.evs ++ [EpochUpdate.insert u v]⟩
    s'.frontier = s.frontier ∧
    EpochSlotInv c U V w s'.frontier pBase metaBase io slack' false sl' s'.mem ∧
    (∀ addr, ¬slotOwnsAddr c w metaBase sl.nCap io addr → s'.mem addr = s.mem addr) ∧
    (io.usePaged = 0 → io.sideBit ≠ 0 →
      s'.mem io.pgL.metaBase = s.mem io.pgL.metaBase ∧
      (SplitHiQuotBounded io (s.mem (metaBase + 1)) s.mem →
        SplitHiQuotBounded io (s'.mem (metaBase + 1)) s'.mem)) ∧
    (io.usePaged ≠ 0 →
      (extractPagePair io.pgL s'.mem).virtLen io.partner.side =
        (extractPagePair io.pgL s.mem).virtLen io.partner.side ∧
      ∀ idx < (extractPagePair io.pgL s.mem).virtLen io.partner.side,
        slotIoPairAt io.partner s'.mem idx = slotIoPairAt io.partner s.mem idx) ∧
    ((sl.nCap = 0 → (liveDom sl.s_abs).card ≤ 2 * whpThreshold c) →
      sl'.GoodCovers →
      memoryCost (epochInsertProg ((pBase, u.val), v.val)) s ≤ epochStepCost c) := by
  dsimp only
  have hm_ns := h.mem_nSide_eq
  have hio_old := h.io_stateInv
  by_cases h0 : sl.nCap = 0
  · have hraw := h; unfold EpochSlotInv at hraw; rw [ite_eq_left h0] at hraw
    obtain ⟨hw6, hp_fr, hv, hpt, hdisj, hst⟩ := hraw
    have hcap_sm : sl.s_abs u = none →
        s.mem (metaBase + 1) < io.pgL.nCap ∧
        (io.usePaged ≠ 0 → (extractPagePair io.pgL s.mem).totalItems + 1 ≤ io.pgL.nCap) :=
      fun hnone => ⟨hm_ns ▸ (hcap_io hnone).1, (hcap_io hnone).2⟩
    obtain ⟨hfr, hc, hpt', hst', hout, hpg⟩ :=
      epochInsertProg_spec_small hv hpt hdisj hst u v hcap_sm
    refine ⟨hfr, ?_, ?_, fun hup hsb => ⟨?_, ?_⟩, hpg, fun hsm _ => ?_⟩
    · unfold EpochSlotInv; dsimp only; rw [ite_eq_left h0]
      exact ⟨hw6, hfr ▸ hp_fr, hfr ▸ hv, hpt', hdisj, hst'⟩
    · intro addr ha
      unfold slotOwnsAddr at ha; rw [ite_eq_left h0] at ha
      exact hout addr ha
    · exact epochInsertProg_preserves_split_cursor_small hv hpt hup hsb u.val v.val
    · intro hhi
      have hns_le : s.mem (metaBase + 1) ≤ io.pgL.nCap := by
        unfold SlotIoLayout.StateInv at hio_old; rw [ite_eq_left hup] at hio_old; exact hio_old.1
      exact epochInsertProg_preserves_hiQuot_small hv hpt hup hsb hns_le hhi u v.val
    · have hc1 := hsm h0; dsimp only at hc; rw [hm_ns] at hc
      unfold epochStepCost smallStepCost
      have hle := le_max_left (21 * (2 * whpThreshold c) + 1600) (largeFastStepCost c)
      omega
  · have hr := h.fastLayoutReady h0
    have hraw := h; unfold EpochSlotInv at hraw; rw [ite_eq_right h0] at hraw
    obtain ⟨hv, hinv, hfp, hcd, hev, hgd⟩ := hraw
    let fl : FastEpochLayout := ⟨c, U, V, w, sl.nCap, metaBase, pBase, io⟩
    have hns_lt : sl.s_abs u = none → s.mem (metaBase + 1) < sl.nCap :=
      fun hnone => hm_ns ▸ hcap_n hnone h0
    have happ : sl.s_abs u = none → io.AppendCap (s.mem (metaBase + 1)) s.mem := fun hnone => by
      unfold SlotIoLayout.AppendCap
      by_cases hup : io.usePaged = 0
      · rw [ite_eq_left hup]; exact hm_ns ▸ (hcap_io hnone).1
      · rw [ite_eq_right hup]; exact (hcap_io hnone).2 hup
    have hcap_lg : sl.s_abs u = none →
        (s.mem (fl.metaBase + 2) = 0 →
          (extractBlockPool fl.mp s.mem).nSide < fl.N ∧
          fl.io.AppendCap (extractBlockPool fl.mp s.mem).nSide s.mem) ∧
        (s.mem (fl.metaBase + 2) = 1 →
          (extractFallback fl.mp s.mem).nSide < fl.N ∧
          fl.io.AppendCap (extractFallback fl.mp s.mem).nSide s.mem) := fun hnone =>
      ⟨fun _ => ⟨hns_lt hnone, happ hnone⟩,
       fun _ => ⟨hns_lt hnone, happ hnone⟩⟩
    obtain ⟨hfr, hinv', hc_lg, hout, hpg⟩ := epochInsertProg_spec_large hv hinv u v hcap_lg
    have hev' : EpochUpdate.eval (sl.evs ++ [EpochUpdate.insert u v]) =
        Function.update sl.s_abs u (some v) := by
      rw [eval_append_singleton, hev]; rfl
    have hcard_last : (liveDom (Function.update sl.s_abs u (some v))).card ≤ sl.nCap := by
      rw [liveDom_insert_card]
      by_cases hnone : sl.s_abs u = none
      · rw [ite_eq_left hnone]; exact hcap_n hnone h0
      · rw [ite_eq_right hnone]
        have hprev := hcd sl.evs.length le_rfl
        rwa [List.take_of_length_le le_rfl, hev] at hprev
    have hcd' := evs_card_append hcd (EpochUpdate.insert u v) (hev'.symm ▸ hcard_last)
    have hgd' : GoodEpochAt fl
        (if io.usePaged = 0 ∨ (extractPageUnperm io.pgL s.mem).cleanPhase = 0 then 0 else 24)
        sl.seeds (sl.evs ++ [EpochUpdate.insert u v])
        ((Memory.spec 0).clientState s (epochInsertProg ((pBase, u.val), v.val))).mem :=
      GoodEpochAt.of_insert hv hgd u v fun hnone _ =>
        ⟨hns_lt (hev ▸ hnone), happ (hev ▸ hnone)⟩
    have hfp' : ((Memory.spec 0).clientState s (epochInsertProg ((pBase, u.val), v.val))).mem
        fl.fpHashBase < 2 ^ (redWidthWhp U - 1) := by
      have hsp_fp := BitPackedDoubleTabulation.space_pos w (cTabWhp c) (dTabWhp c)
        (bCharWhp sl.nCap) (fpBitsWhp sl.nCap)
      rw [hout fl.fpHashBase (hv.not_ownsFast_seeds
        (by dsimp only [fl, FastEpochLayout.fpHashBase]; unfold offFpHash offBktHash; omega)
        (by dsimp only [fl, FastEpochLayout.fpHashBase]; unfold offBktMeta offFpHash; omega))]
      exact hfp
    have hsl' : EpochSlotInv c U V w
        ((Memory.spec 0).clientState s (epochInsertProg ((pBase, u.val), v.val))).frontier
        pBase metaBase io
        (if io.usePaged = 0 ∨ (extractPageUnperm io.pgL s.mem).cleanPhase = 0 then 0 else 24)
        false ⟨sl.nCap, Function.update sl.s_abs u (some v), sl.seeds,
          sl.evs ++ [EpochUpdate.insert u v]⟩
        ((Memory.spec 0).clientState s (epochInsertProg ((pBase, u.val), v.val))).mem := by
      unfold EpochSlotInv; dsimp only; rw [ite_eq_right h0]
      exact ⟨hfr ▸ hv, hinv', hfp', hcd', hev', hgd'⟩
    refine ⟨hfr, hsl', ?_, fun hup hsb => ⟨?_, ?_⟩, fun hup => ⟨(hpg hup).1, (hpg hup).2.2⟩,
      fun _ hgc' => hc_lg (hsl'.mode_zero_of_goodCovers h0 hgc')⟩
    · intro addr ha
      unfold slotOwnsAddr at ha; rw [ite_eq_right h0] at ha
      exact hout addr (fun hf => ha (by
        rcases hf with h1 | h2 | h3
        · exact Or.inl h1
        · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr h3)))
    · exact epochInsertProg_preserves_split_cursor_large hr hup hsb u.val v.val
    · intro hhi
      have hns' := hsl'.mem_nSide_eq
      dsimp only at hns'
      have hio_s' := hsl'.io_stateInv
      unfold SlotIoLayout.StateInv at hio_s'; rw [ite_eq_left hup] at hio_s'
      refine epochInsertProg_preserves_hiQuot_large hr hup hsb ⟨?_, hio_s'.1⟩ hhi
      rw [hns', hm_ns, liveDom_insert_card]
      split_ifs <;> omega

/-- Uniform specification of `epochDeleteProg` on an `EpochSlotInv` slot (`draining = false` or
`draining = true`). -/
theorem EpochSlotInv.delete_spec {c U V w pBase metaBase : ℕ} {io : SlotIoLayout}
    {draining : Bool} {sl : SlotLatent c U V} {s : Memory.State}
    (h : EpochSlotInv c U V w s.frontier pBase metaBase io 0 draining sl s.mem)
    (u : Fin U) :
    let s' := (Memory.spec 0).clientState s (epochDeleteProg (pBase, u.val))
    let slack' :=
      if io.usePaged = 0 ∨ (extractPageUnperm io.pgL s.mem).cleanPhase = 0 then 0 else 24
    let evs' := if draining then sl.evs else sl.evs ++ [EpochUpdate.delete u]
    let sl' : SlotLatent c U V := ⟨sl.nCap, Function.update sl.s_abs u none, sl.seeds, evs'⟩
    s'.frontier = s.frontier ∧
    EpochSlotInv c U V w s'.frontier pBase metaBase io slack' draining sl' s'.mem ∧
    (∀ addr, ¬slotOwnsAddr c w metaBase sl.nCap io addr → s'.mem addr = s.mem addr) ∧
    (io.usePaged = 0 → io.sideBit ≠ 0 →
      s'.mem io.pgL.metaBase = s.mem io.pgL.metaBase ∧
      (SplitHiQuotBounded io (s.mem (metaBase + 1)) s.mem →
        SplitHiQuotBounded io (s'.mem (metaBase + 1)) s'.mem)) ∧
    (io.usePaged ≠ 0 →
      (extractPagePair io.pgL s'.mem).virtLen io.partner.side =
        (extractPagePair io.pgL s.mem).virtLen io.partner.side ∧
      ∀ idx < (extractPagePair io.pgL s.mem).virtLen io.partner.side,
        slotIoPairAt io.partner s'.mem idx = slotIoPairAt io.partner s.mem idx) ∧
    ((sl.nCap = 0 → (liveDom sl.s_abs).card ≤ 2 * whpThreshold c) →
      sl'.GoodCovers →
      memoryCost (epochDeleteProg (pBase, u.val)) s ≤ epochStepCost c) := by
  dsimp only
  have hm_ns := h.mem_nSide_eq
  have hio_old := h.io_stateInv
  by_cases h0 : sl.nCap = 0
  · have hraw := h; unfold EpochSlotInv at hraw; rw [ite_eq_left h0] at hraw
    obtain ⟨hw6, hp_fr, hv, hpt, hdisj, hst⟩ := hraw
    obtain ⟨hfr, hc, hpt', hst', hout, hpg⟩ := epochDeleteProg_spec_small hv hpt hdisj hst u
    refine ⟨hfr, ?_, ?_, fun hup hsb => ⟨?_, ?_⟩, hpg, fun hsm _ => ?_⟩
    · unfold EpochSlotInv; dsimp only; rw [ite_eq_left h0]
      exact ⟨hw6, hfr ▸ hp_fr, hfr ▸ hv, hpt', hdisj, hst'⟩
    · intro addr ha
      unfold slotOwnsAddr at ha; rw [ite_eq_left h0] at ha
      exact hout addr ha
    · exact epochDeleteProg_preserves_split_cursor_small hv hpt hup hsb u.val
    · intro hhi
      have hns_le : s.mem (metaBase + 1) ≤ io.pgL.nCap := by
        unfold SlotIoLayout.StateInv at hio_old; rw [ite_eq_left hup] at hio_old; exact hio_old.1
      exact epochDeleteProg_preserves_hiQuot_small hv hpt hup hsb hns_le hhi u.val
    · have hc1 := hsm h0; dsimp only at hc; rw [hm_ns] at hc
      unfold epochStepCost smallStepCost
      have hle := le_max_left (21 * (2 * whpThreshold c) + 1600) (largeFastStepCost c)
      omega
  · have hr := h.fastLayoutReady h0
    have hraw := h; unfold EpochSlotInv at hraw; rw [ite_eq_right h0] at hraw
    obtain ⟨hv, hinv, hfp, hcd, hgd⟩ := hraw
    let fl : FastEpochLayout := ⟨c, U, V, w, sl.nCap, metaBase, pBase, io⟩
    obtain ⟨hfr, hinv', hfast, hout, hpg⟩ := epochDeleteProg_spec_large hv hinv u
    have hfp' : ((Memory.spec 0).clientState s (epochDeleteProg (pBase, u.val))).mem
        fl.fpHashBase < 2 ^ (redWidthWhp U - 1) := by
      have hsp_fp := BitPackedDoubleTabulation.space_pos w (cTabWhp c) (dTabWhp c)
        (bCharWhp sl.nCap) (fpBitsWhp sl.nCap)
      rw [hout fl.fpHashBase (hv.not_ownsFast_seeds
        (by dsimp only [fl, FastEpochLayout.fpHashBase]; unfold offFpHash offBktHash; omega)
        (by dsimp only [fl, FastEpochLayout.fpHashBase]; unfold offBktMeta offFpHash; omega))]
      exact hfp
    have hsl' : EpochSlotInv c U V w
        ((Memory.spec 0).clientState s (epochDeleteProg (pBase, u.val))).frontier
        pBase metaBase io
        (if io.usePaged = 0 ∨ (extractPageUnperm io.pgL s.mem).cleanPhase = 0 then 0 else 24)
        draining
        ⟨sl.nCap, Function.update sl.s_abs u none, sl.seeds,
          if draining then sl.evs else sl.evs ++ [EpochUpdate.delete u]⟩
        ((Memory.spec 0).clientState s (epochDeleteProg (pBase, u.val))).mem := by
      unfold EpochSlotInv; dsimp only; rw [ite_eq_right h0]
      cases draining
      · dsimp only [Bool.false_eq_true, ↓reduceIte] at hgd ⊢
        have hev' : EpochUpdate.eval (sl.evs ++ [EpochUpdate.delete u]) =
            Function.update sl.s_abs u none := by
          rw [eval_append_singleton, hgd.1]; rfl
        have hcard_last : (liveDom (Function.update sl.s_abs u none)).card ≤ sl.nCap := by
          rw [liveDom_delete_card]
          have hprev := hcd sl.evs.length le_rfl
          rw [List.take_of_length_le le_rfl, hgd.1] at hprev
          split_ifs <;> omega
        exact ⟨hfr ▸ hv, hinv', hfp',
          evs_card_append hcd (EpochUpdate.delete u) (hev'.symm ▸ hcard_last),
          hev', GoodEpochAt.of_delete hv hgd.2 u⟩
      · dsimp only [↓reduceIte] at hgd ⊢
        exact ⟨hfr ▸ hv, hinv', hfp', hcd, fun hgc => (hfast (hgd hgc)).1⟩
    refine ⟨hfr, hsl', ?_, fun hup hsb => ⟨?_, ?_⟩, fun hup => ⟨(hpg hup).1, (hpg hup).2.2⟩,
      fun _ hgc' => ?_⟩
    · intro addr ha
      unfold slotOwnsAddr at ha; rw [ite_eq_right h0] at ha
      exact hout addr (fun hf => ha (by
        rcases hf with h1 | h2 | h3
        · exact Or.inl h1
        · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr h3)))
    · exact epochDeleteProg_preserves_split_cursor_large hr hup hsb u.val
    · intro hhi
      have hns' := hsl'.mem_nSide_eq; dsimp only at hns'
      have hio_s' := hsl'.io_stateInv
      unfold SlotIoLayout.StateInv at hio_s'; rw [ite_eq_left hup] at hio_s'
      refine epochDeleteProg_preserves_hiQuot_large hr hup hsb ⟨?_, hio_s'.1⟩ hhi
      rw [hns', hm_ns, liveDom_delete_card]
      split_ifs <;> omega
    · cases draining
      · dsimp only [Bool.false_eq_true, ↓reduceIte] at hgd hgc'
        obtain ⟨win, hgood', hcov'⟩ := hgc' hv.thresh_le
        exact (hfast (hgd.2 win hgood' hcov'.of_append).1).2
      · dsimp only [↓reduceIte] at hgd hgc'
        exact (hfast (hgd hgc')).2

/-- Uniform specification of `epochPopAnyProg` on a draining (`draining = true`) `EpochSlotInv`
slot with `0 < (liveDom sl.s_abs).card`. -/
theorem EpochSlotInv.popAny_spec {c U V w pBase metaBase : ℕ} {io : SlotIoLayout}
    {sl : SlotLatent c U V} {s : Memory.State}
    (h : EpochSlotInv c U V w s.frontier pBase metaBase io 0 true sl s.mem)
    (hpos : 0 < (liveDom sl.s_abs).card) :
    let res := (Memory.spec 0).clientResult s (epochPopAnyProg pBase)
    let s' := (Memory.spec 0).clientState s (epochPopAnyProg pBase)
    let slack' :=
      if io.usePaged = 0 ∨ (extractPageUnperm io.pgL s.mem).cleanPhase = 0 then 0 else 24
    ∃ (u : Fin U) (v : Fin V),
      res = (u.val, v.val) ∧ sl.s_abs u = some v ∧
      s'.frontier = s.frontier ∧
      EpochSlotInv c U V w s'.frontier pBase metaBase io slack' true
        ⟨sl.nCap, Function.update sl.s_abs u none, sl.seeds, sl.evs⟩ s'.mem ∧
      (∀ addr, ¬slotOwnsAddr c w metaBase sl.nCap io addr → s'.mem addr = s.mem addr) ∧
      (io.usePaged ≠ 0 →
        (extractPagePair io.pgL s'.mem).virtLen io.partner.side =
          (extractPagePair io.pgL s.mem).virtLen io.partner.side ∧
        (extractPagePair io.pgL s'.mem).totalItems =
          (extractPagePair io.pgL s.mem).totalItems - 1 ∧
        ∀ idx < (extractPagePair io.pgL s.mem).virtLen io.partner.side,
          slotIoPairAt io.partner s'.mem idx = slotIoPairAt io.partner s.mem idx) ∧
      (sl.GoodCovers →
        memoryCost (epochPopAnyProg pBase) s ≤ epochStepCost c) := by
  dsimp only
  have hm_ns := h.mem_nSide_eq
  by_cases h0 : sl.nCap = 0
  · have hraw := h; unfold EpochSlotInv at hraw; rw [ite_eq_left h0] at hraw
    obtain ⟨hw6, hp_fr, hv, hpt, hdisj, hst⟩ := hraw
    obtain ⟨u, v, hres, hsu, hfr, hc, hpt', _, hst', hout, hpg⟩ :=
      epochPopAnyProg_spec_small hv hpt hdisj hst (hm_ns.symm ▸ hpos)
    refine ⟨u, v, hres, hsu, hfr, ?_, ?_, hpg, fun _ => ?_⟩
    · unfold EpochSlotInv; dsimp only; rw [ite_eq_left h0]
      exact ⟨hw6, hfr ▸ hp_fr, hfr ▸ hv, hpt', hdisj, hst'⟩
    · intro addr ha
      unfold slotOwnsAddr at ha; rw [ite_eq_left h0] at ha
      exact hout addr ha
    · unfold epochStepCost smallStepCost
      have hle := le_max_left (21 * (2 * whpThreshold c) + 1600) (largeFastStepCost c)
      omega
  · have hraw := h; unfold EpochSlotInv at hraw; rw [ite_eq_right h0] at hraw
    obtain ⟨hv, hinv, hfp, hcd, hgd⟩ := hraw
    dsimp only [↓reduceIte] at hgd
    let fl : FastEpochLayout := ⟨c, U, V, w, sl.nCap, metaBase, pBase, io⟩
    have hpos_m : 0 < s.mem (metaBase + 1) := hm_ns.symm ▸ hpos
    obtain ⟨u, v, hres, hsu, hfr, hinv', hfast, hout, hpg⟩ :=
      epochPopAnyProg_spec_large hv hinv ⟨fun _ => hpos_m, fun _ => hpos_m⟩
    have hfp' : ((Memory.spec 0).clientState s (epochPopAnyProg pBase)).mem
        fl.fpHashBase < 2 ^ (redWidthWhp U - 1) := by
      have hsp_fp := BitPackedDoubleTabulation.space_pos w (cTabWhp c) (dTabWhp c)
        (bCharWhp sl.nCap) (fpBitsWhp sl.nCap)
      rw [hout fl.fpHashBase (hv.not_ownsFast_seeds
        (by dsimp only [fl, FastEpochLayout.fpHashBase]; unfold offFpHash offBktHash; omega)
        (by dsimp only [fl, FastEpochLayout.fpHashBase]; unfold offBktMeta offFpHash; omega))]
      exact hfp
    refine ⟨u, v, hres, hsu, hfr, ?_, ?_, hpg, fun hgc => (hfast (hgd hgc)).2⟩
    · unfold EpochSlotInv; dsimp only; rw [ite_eq_right h0]
      exact ⟨hfr ▸ hv, hinv', hfp', hcd, fun hgc => (hfast (hgd hgc)).1⟩
    · intro addr ha
      unfold slotOwnsAddr at ha; rw [ite_eq_right h0] at ha
      exact hout addr (fun hf => ha (by
        rcases hf with h1 | h2 | h3
        · exact Or.inl h1
        · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr h3)))

/-! ## Section 4: `initDualRootProg` (`194`-Word Empty Arena Initializer, `¬ReadsWidth`) -/

private def initU1Val (U : ℕ) : ℕ := U - 1
private def initV1Val (V : ℕ) : ℕ := V - 1
private def initKeyBitsVal (U : ℕ) : ℕ := keyBits U
private def initValBitsVal (V : ℕ) : ℕ := valBits V
private def initRedWVal (U : ℕ) : ℕ := redWidthWhp U
private def initThreshVal (c U : ℕ) : ℕ := if whpThreshold c ≤ U then whpThreshold c else 0
private def initCTabVal (c U : ℕ) : ℕ := if whpThreshold c ≤ U then cTabWhp c else 0
private def initDTabVal (c U : ℕ) : ℕ := if whpThreshold c ≤ U then dTabWhp c else 0
private def initCEffVal (c U : ℕ) : ℕ := if whpThreshold c ≤ U then cEff c else 0

private theorem initU1Val_eq (U : ℕ) : initU1Val U = U - 1 := rfl
private theorem initV1Val_eq (V : ℕ) : initV1Val V = V - 1 := rfl
private theorem initKeyBitsVal_eq (U : ℕ) : initKeyBitsVal U = keyBits U := rfl
private theorem initValBitsVal_eq (V : ℕ) : initValBitsVal V = valBits V := rfl
private theorem initRedWVal_eq (U : ℕ) : initRedWVal U = redWidthWhp U := rfl

private theorem initThreshVal_eq (c U : ℕ) :
    initThreshVal c U = (if whpThreshold c ≤ U then whpThreshold c else 0) := rfl

private theorem initCTabVal_eq (c U : ℕ) :
    initCTabVal c U = (if whpThreshold c ≤ U then cTabWhp c else 0) := rfl

private theorem initDTabVal_eq (c U : ℕ) :
    initDTabVal c U = (if whpThreshold c ≤ U then dTabWhp c else 0) := rfl

private theorem initCEffVal_eq (c U : ℕ) :
    initCEffVal c U = (if whpThreshold c ≤ U then cEff c else 0) := rfl

private theorem static_hdr_fits {c U V w : ℕ}
    (hw11 : 11 ≤ w) (hU0 : 0 < U) (hUw : U < 2 ^ w) (hV0 : 0 < V) (hVw : V ≤ 2 ^ w) :
    Fits w (initU1Val U) ∧ Fits w (initV1Val V) ∧ Fits w w ∧
    keyBits U ≤ w ∧ Fits w (initKeyBitsVal U) ∧ valBits V ≤ w ∧ Fits w (initValBitsVal V) ∧
    redWidthWhp U ≤ w ∧ Fits w (initRedWVal U) ∧
    Fits w (initThreshVal c U) ∧ Fits w (initCTabVal c U) ∧
    Fits w (initDTabVal c U) ∧ Fits w (initCEffVal c U) := by
  have hw_lt : w < 2 ^ w := Nat.lt_two_pow_self
  have hkb_le : keyBits U ≤ w := Nat.clog_le_of_le_pow hUw.le
  have hvb_le : valBits V ≤ w := Nat.clog_le_of_le_pow hVw
  have hrw_le : redWidthWhp U ≤ w := max_le (by omega) hkb_le
  have hz : Fits w 0 := Nat.two_pow_pos w
  have hf_th : Fits w (initThreshVal c U) := by
    unfold initThreshVal
    by_cases hth : whpThreshold c ≤ U
    · rw [ite_eq_left hth]; exact lt_of_le_of_lt hth hUw
    · rw [ite_eq_right hth]; exact hz
  have h4c_lt : whpThreshold c ≤ U → 4 * (cTabWhp c + 2) < w ∧ dTabWhp c < w := fun hth => by
    have hct := le_cTabWhp c
    have hqt := le_qTabWhp c
    have hce := codeExpWhp_mul_ell_le_bCharWhp hth
    have hell := Dynamic.one_le_logLogFactor U
    have hpb := largeEpoch_param_bounds hth le_rfl hUw
    have hbc_w : bCharWhp U < w := hpb.2.2.2.1
    have h2 : cTabWhp c + 1 ≤ (cTabWhp c + 1) ^ 2 := by
      rw [sq]; exact Nat.le_mul_of_pos_right _ (by omega)
    have hsq1 : 4 * (cTabWhp c + 2) ≤ 16 * (cTabWhp c + 1) ^ 2 * qTabWhp c := by
      have h3 : 4 * (cTabWhp c + 2) ≤ 16 * (cTabWhp c + 1) ^ 2 := by omega
      exact h3.trans (Nat.le_mul_of_pos_right _ (by omega))
    have hd1 : dTabWhp c ≤ 16 * (cTabWhp c + 1) ^ 2 * qTabWhp c := by
      unfold dTabWhp
      calc (2 * qTabWhp c) * (cTabWhp c + 1)
          = 2 * (cTabWhp c + 1) * qTabWhp c := by ring
        _ ≤ 16 * (cTabWhp c + 1) ^ 2 * qTabWhp c :=
          Nat.mul_le_mul_right _ (by omega)
    have hcb : 16 * (cTabWhp c + 1) ^ 2 * qTabWhp c ≤ codeExpWhp c := by
      rw [codeExpWhp_eq]; omega
    have hmul : codeExpWhp c ≤ codeExpWhp c * Dynamic.logLogFactor U :=
      Nat.le_mul_of_pos_right _ hell
    exact ⟨by omega, by omega⟩
  have hf_ct : Fits w (initCTabVal c U) := by
    unfold initCTabVal
    by_cases hth : whpThreshold c ≤ U
    · rw [ite_eq_left hth]; have := (h4c_lt hth).1; dsimp only [Fits] at hw_lt ⊢; omega
    · rw [ite_eq_right hth]; exact hz
  have hf_dt : Fits w (initDTabVal c U) := by
    unfold initDTabVal
    by_cases hth : whpThreshold c ≤ U
    · rw [ite_eq_left hth]; have := (h4c_lt hth).2; dsimp only [Fits] at hw_lt ⊢; omega
    · rw [ite_eq_right hth]; exact hz
  have hf_ce : Fits w (initCEffVal c U) := by
    unfold initCEffVal
    by_cases hth : whpThreshold c ≤ U
    · rw [ite_eq_left hth]; have := (h4c_lt hth).1
      have hce_le : cEff c ≤ cTabWhp c := by unfold cTabWhp; omega
      dsimp only [Fits] at hw_lt ⊢; omega
    · rw [ite_eq_right hth]; exact hz
  unfold initU1Val initV1Val initKeyBitsVal initValBitsVal initRedWVal
  dsimp only [Fits] at hw_lt hUw hVw ⊢
  exact ⟨by omega, by omega, hw_lt, hkb_le, by omega, hvb_le, by omega, hrw_le, by omega,
    hf_th, hf_ct, hf_dt, hf_ce⟩

attribute [local irreducible] initU1Val initV1Val initKeyBitsVal initValBitsVal initRedWVal
attribute [local irreducible] initThreshVal initCTabVal initDTabVal initCEffVal

private def writeAtBaseProg : (ℕ × ℕ) × ℕ → Memory.Prog Unit
  | ((base, off), val) => Memory.write (base + off) val

private theorem realizesBounded_writeAtBase :
    RealizesBounded .exact writeAtBaseProg
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun _ ((base, off), _) s => base + off < s.frontier)
      (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨⟨base, off⟩, val⟩
    have hfr_w : s.frontier < 2 ^ w := hmem.1
    dsimp only [Prod.fst, Prod.snd, Fits] at *
    omega)

private def writeAddAtBaseProg : (ℕ × ℕ) × ℕ → Memory.Prog Unit
  | ((base, off), addOff) => Memory.write (base + off) (base + addOff)

private theorem realizesBounded_writeAddAtBase :
    RealizesBounded .exact writeAddAtBaseProg
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun _ ((base, off), addOff) s => base + off < s.frontier ∧ base + addOff ≤ s.frontier)
      (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨⟨base, off⟩, addOff⟩
    have hfr_w : s.frontier < 2 ^ w := hmem.1
    dsimp only [Prod.fst, Prod.snd, Fits] at *
    omega)

private theorem fin_width_nat_zero (i : Fin (WordEncoding.width ℕ)) : i = ⟨0, by decide⟩ :=
  Fin.ext (by have hi := i.isLt; change i.val < 1 at hi; dsimp only; omega)

private theorem realizesBounded_pureConstGen {δ : Type} {k : ℕ}
    (input : δ ↪ (Fin k → ℕ)) (z : ℕ) :
    RealizesBounded .exact (fun _ : δ => (pure z : Memory.Prog ℕ))
      input (WordEncoding.encode (α := ℕ))
      (fun w _ _ => Fits w z) (fun _ _ => 0) :=
  (RealizesBounded.pure₀ (B := .exact) input (WordEncoding.encode (α := ℕ))
    (fun _ => z) (fun _ _ => z) (P := fun _ => True) (bound := fun _ => z)
    (fun w _ => Fits w z)
    (fun _ i => by rw [fin_width_nat_zero i]; rfl)
    (fun _ => GlueComputable.const z (fun _ _ => le_rfl))
    (fun _ _ _ _ h => h)).consequence (fun _ _ _ _ _ h => ⟨trivial, h⟩) (fun _ _ => le_rfl)

private def writeConstAtProg (off val : ℕ) (base : ℕ) : Memory.Prog Unit :=
  PFunctor.FreeM.bind (pure off) fun o =>
    PFunctor.FreeM.bind (pure val) fun v => writeAtBaseProg ((base, o), v)

private theorem realizesBounded_writeConstAt (off val : ℕ) :
    RealizesBounded .exact (writeConstAtProg off val)
      (WordEncoding.encode (α := ℕ)) (WordEncoding.encode (α := Unit))
      (fun w base s => Fits w off ∧ Fits w val ∧ base + off < s.frontier)
      (fun _ _ => 0) :=
  (RealizesBounded.bind₀ (realizesBounded_pureConstGen _ off)
    (RealizesBounded.bind₀ (realizesBounded_pureConstGen _ val)
      realizesBounded_writeAtBase)).consequence
    (fun _ _ _ _ _ ⟨ho, hv, hfr⟩ => ⟨ho, hv, hfr⟩) (fun _ _ => le_rfl)

private def writeAddConstAtProg (off addOff : ℕ) (base : ℕ) : Memory.Prog Unit :=
  PFunctor.FreeM.bind (pure off) fun o =>
    PFunctor.FreeM.bind (pure addOff) fun a => writeAddAtBaseProg ((base, o), a)

private theorem realizesBounded_writeAddConstAt (off addOff : ℕ) :
    RealizesBounded .exact (writeAddConstAtProg off addOff)
      (WordEncoding.encode (α := ℕ)) (WordEncoding.encode (α := Unit))
      (fun w base s =>
        Fits w off ∧ Fits w addOff ∧ base + off < s.frontier ∧ base + addOff ≤ s.frontier)
      (fun _ _ => 0) :=
  (RealizesBounded.bind₀ (realizesBounded_pureConstGen _ off)
    (RealizesBounded.bind₀ (realizesBounded_pureConstGen _ addOff)
      realizesBounded_writeAddAtBase)).consequence
    (fun _ _ _ _ _ ⟨ho, ha, hf1, hf2⟩ => ⟨ho, ha, hf1, hf2⟩) (fun _ _ => le_rfl)

private def seqUnit (p₁ p₂ : ℕ → Memory.Prog Unit) (base : ℕ) : Memory.Prog Unit :=
  PFunctor.FreeM.bind (p₁ base) fun _ => p₂ base

private theorem realizesBounded_seqUnit
    {p₁ p₂ : ℕ → Memory.Prog Unit} {safe₁ safe₂ : ℕ → ℕ → Memory.State → Prop}
    (h₁ : RealizesBounded .exact p₁ (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := Unit)) safe₁ (fun _ _ => 0))
    (h₂ : RealizesBounded .exact p₂ (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := Unit)) safe₂ (fun _ _ => 0)) :
    RealizesBounded .exact (seqUnit p₁ p₂)
      (WordEncoding.encode (α := ℕ)) (WordEncoding.encode (α := Unit))
      (fun w b s => safe₁ w b s ∧ safe₂ w b ((Memory.spec 0).clientState s (p₁ b)))
      (fun _ _ => 0) :=
  RealizesBounded.bind₀ h₁
    (h₂.reindex Prod.fst _ (fun i => ⟨i.val, by have hi := i.isLt; change i.val < 1 at hi; omega⟩)
      (fun ⟨_, _⟩ i => by rw [fin_width_nat_zero i]; rfl))

private def writeSmallConstAProg (offP offM kb : ℕ) : ℕ → Memory.Prog Unit :=
  seqUnit (writeConstAtProg offP 0) <|
  seqUnit (writeAddConstAtProg (offP + 1) offM) <|
  seqUnit (writeConstAtProg (offP + 48) 0) <|
  seqUnit (writeConstAtProg (offP + 49) 0) <|
  seqUnit (writeAddConstAtProg (offP + 50) hdrSplit) <|
  seqUnit (writeAddConstAtProg (offP + 51) 192) <|
  seqUnit (writeConstAtProg (offP + 52) kb)
    (writeConstAtProg (offP + 53) 1)

private def writeSmallConstBProg (offP wv vb kb : ℕ) : ℕ → Memory.Prog Unit :=
  seqUnit (writeConstAtProg (offP + 54) wv) <|
  seqUnit (writeConstAtProg (offP + 55) 32) <|
  seqUnit (writeConstAtProg (offP + 56) 4) <|
  seqUnit (writeAddConstAtProg (offP + 57) 192) <|
  seqUnit (writeConstAtProg (offP + 58) kb) <|
  seqUnit (writeConstAtProg (offP + 59) vb)
    (writeConstAtProg (offP + 60) 0)

private def writeSmallConstProg (offP offM wv vb kb : ℕ) : ℕ → Memory.Prog Unit :=
  seqUnit (writeSmallConstAProg offP offM kb) (writeSmallConstBProg offP wv vb kb)

private def initRootStaticAProg (c U V w : ℕ) : ℕ → Memory.Prog Unit :=
  seqUnit (writeConstAtProg hdrU1 (initU1Val U)) <|
  seqUnit (writeConstAtProg hdrV1 (initV1Val V)) <|
  seqUnit (writeConstAtProg hdrW w) <|
  seqUnit (writeConstAtProg hdrKeyBits (initKeyBitsVal U)) <|
  seqUnit (writeConstAtProg hdrValBits (initValBitsVal V)) <|
  seqUnit (writeConstAtProg hdrThresh (initThreshVal c U))
    (writeConstAtProg hdrCTab (initCTabVal c U))

private def initRootStaticBProg (c U : ℕ) : ℕ → Memory.Prog Unit :=
  seqUnit (writeConstAtProg hdrDTab (initDTabVal c U)) <|
  seqUnit (writeConstAtProg hdrRedW (initRedWVal U)) <|
  seqUnit (writeConstAtProg hdrCEff (initCEffVal c U)) <|
  seqUnit (writeAddConstAtProg hdrItemLo 192) <|
  seqUnit (writeAddConstAtProg hdrItemHi 192) <|
  seqUnit (writeConstAtProg hdrQLo (initKeyBitsVal U))
    (writeConstAtProg hdrQHi (initKeyBitsVal U))

private theorem cstate_writeConstAt (off val base : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (writeConstAtProg off val base) =
      { mem := Function.update s.mem (base + off) val, frontier := s.frontier } := rfl

private theorem cstate_writeAddConstAt (off addOff base : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (writeAddConstAtProg off addOff base) =
      { mem := Function.update s.mem (base + off) (base + addOff), frontier := s.frontier } := rfl

private theorem cstate_seqUnit (p₁ p₂ : ℕ → Memory.Prog Unit) (base : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (seqUnit p₁ p₂ base) =
      (Memory.spec 0).clientState ((Memory.spec 0).clientState s (p₁ base)) (p₂ base) :=
  StateTransitionSpec.clientState_bind _ _ _

private theorem mcost_seqUnit (p₁ p₂ : ℕ → Memory.Prog Unit) (base : ℕ) (s : Memory.State) :
    memoryCost (seqUnit p₁ p₂ base) s =
      memoryCost (p₁ base) s + memoryCost (p₂ base) ((Memory.spec 0).clientState s (p₁ base)) :=
  Realization.memoryCost_bind' _ _ _

private theorem mcost_writeConstAt (off val base : ℕ) (s : Memory.State) :
    memoryCost (writeConstAtProg off val base) s = 1 := rfl

private theorem mcost_writeAddConstAt (off addOff base : ℕ) (s : Memory.State) :
    memoryCost (writeAddConstAtProg off addOff base) s = 1 := rfl

private theorem initRootStaticA_fr (c U V w base : ℕ) (s : Memory.State) :
    ((Memory.spec 0).clientState s (initRootStaticAProg c U V w base)).frontier = s.frontier := by
  unfold initRootStaticAProg
  repeat rw [cstate_seqUnit]
  repeat rw [cstate_writeConstAt]

private theorem initRootStaticB_fr (c U base : ℕ) (s : Memory.State) :
    ((Memory.spec 0).clientState s (initRootStaticBProg c U base)).frontier = s.frontier := by
  unfold initRootStaticBProg
  repeat rw [cstate_seqUnit]
  repeat (first | rw [cstate_writeConstAt] | rw [cstate_writeAddConstAt])

private theorem initRootStaticA_mc (c U V w base : ℕ) (s : Memory.State) :
    memoryCost (initRootStaticAProg c U V w base) s = 7 := by
  unfold initRootStaticAProg
  simp only [mcost_seqUnit, mcost_writeConstAt]

private theorem initRootStaticB_mc (c U base : ℕ) (s : Memory.State) :
    memoryCost (initRootStaticBProg c U base) s = 7 := by
  unfold initRootStaticBProg
  simp only [mcost_seqUnit, mcost_writeConstAt, mcost_writeAddConstAt]

private theorem realizesBounded_initRootStaticA (c U V w_p : ℕ) :
    RealizesBounded .exact (initRootStaticAProg c U V w_p)
      (WordEncoding.encode (α := ℕ)) (WordEncoding.encode (α := Unit))
      (fun w base s =>
        w = w_p ∧ 11 ≤ w ∧ 0 < U ∧ U < 2 ^ w ∧ 0 < V ∧ V ≤ 2 ^ w ∧ base + 32 ≤ s.frontier)
      (fun _ _ => 0) :=
  (realizesBounded_seqUnit (realizesBounded_writeConstAt hdrU1 (initU1Val U)) <|
   realizesBounded_seqUnit (realizesBounded_writeConstAt hdrV1 (initV1Val V)) <|
   realizesBounded_seqUnit (realizesBounded_writeConstAt hdrW w_p) <|
   realizesBounded_seqUnit (realizesBounded_writeConstAt hdrKeyBits (initKeyBitsVal U)) <|
   realizesBounded_seqUnit (realizesBounded_writeConstAt hdrValBits (initValBitsVal V)) <|
   realizesBounded_seqUnit (realizesBounded_writeConstAt hdrThresh (initThreshVal c U))
     (realizesBounded_writeConstAt hdrCTab (initCTabVal c U))).consequence
    (fun w base s _ _ ⟨rfl, hw11, hU0, hUw, hV0, hVw, hb⟩ => by
      obtain ⟨fU, fV, fw, _, fkb, _, fvb, _, _, fth, fct, _, _⟩ :=
        static_hdr_fits (c := c) hw11 hU0 hUw hV0 hVw
      have h2w : 2048 ≤ 2 ^ w :=
        (by decide : 2048 = 2 ^ 11) ▸ Nat.pow_le_pow_right (by decide) hw11
      repeat rw [cstate_writeConstAt]
      dsimp only [hdrU1, hdrV1, hdrW, hdrKeyBits, hdrValBits, hdrThresh, hdrCTab, Fits] at *
      exact ⟨⟨by omega, fU, by omega⟩, ⟨by omega, fV, by omega⟩, ⟨by omega, fw, by omega⟩,
        ⟨by omega, fkb, by omega⟩, ⟨by omega, fvb, by omega⟩, ⟨by omega, fth, by omega⟩,
        ⟨by omega, fct, by omega⟩⟩)
    (fun _ _ => le_rfl)

private theorem realizesBounded_initRootStaticB (c U : ℕ) :
    RealizesBounded .exact (initRootStaticBProg c U)
      (WordEncoding.encode (α := ℕ)) (WordEncoding.encode (α := Unit))
      (fun w base s => 11 ≤ w ∧ 0 < U ∧ U < 2 ^ w ∧ base + 194 ≤ s.frontier)
      (fun _ _ => 0) :=
  (realizesBounded_seqUnit (realizesBounded_writeConstAt hdrDTab (initDTabVal c U)) <|
   realizesBounded_seqUnit (realizesBounded_writeConstAt hdrRedW (initRedWVal U)) <|
   realizesBounded_seqUnit (realizesBounded_writeConstAt hdrCEff (initCEffVal c U)) <|
   realizesBounded_seqUnit (realizesBounded_writeAddConstAt hdrItemLo 192) <|
   realizesBounded_seqUnit (realizesBounded_writeAddConstAt hdrItemHi 192) <|
   realizesBounded_seqUnit (realizesBounded_writeConstAt hdrQLo (initKeyBitsVal U))
     (realizesBounded_writeConstAt hdrQHi (initKeyBitsVal U))).consequence
    (fun w base s _ _ ⟨hw11, hU0, hUw, hb⟩ => by
      obtain ⟨_, _, _, _, fkb, _, _, _, frw, _, _, fdt, fce⟩ :=
        static_hdr_fits (c := c) (V := 1) hw11 hU0 hUw Nat.one_pos Nat.one_le_two_pow
      have h2w : 2048 ≤ 2 ^ w :=
        (by decide : 2048 = 2 ^ 11) ▸ Nat.pow_le_pow_right (by decide) hw11
      repeat (first | rw [cstate_writeConstAt] | rw [cstate_writeAddConstAt])
      dsimp only [hdrDTab, hdrRedW, hdrCEff, hdrItemLo, hdrItemHi, hdrQLo, hdrQHi, Fits] at *
      exact ⟨⟨by omega, fdt, by omega⟩, ⟨by omega, frw, by omega⟩, ⟨by omega, fce, by omega⟩,
        ⟨by omega, by omega, by omega, by omega⟩, ⟨by omega, by omega, by omega, by omega⟩,
        ⟨by omega, fkb, by omega⟩, ⟨by omega, fkb, by omega⟩⟩)
    (fun _ _ => le_rfl)

private theorem vh_seqUnit {w base : ℕ} {p₁ p₂ : ℕ → Memory.Prog Unit} {s : Memory.State}
    (h₁ : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p₁ base)))
    (h₂ : (Memory.spec w).ValidHistory ((Memory.spec 0).clientState s (p₁ base))
      ((Memory.spec w).clientHistory ((Memory.spec 0).clientState s (p₁ base)) (p₂ base))) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (seqUnit p₁ p₂ base)) := by
  unfold seqUnit
  rw [validHistory_bind, clientState_width]
  exact ⟨h₁, h₂⟩

private theorem vh_writeConstAt {w off val base : ℕ} {s : Memory.State}
    (ha : base + off < s.frontier) (hv : Fits w val) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (writeConstAtProg off val base)) :=
  ⟨⟨ha, hv⟩, trivial⟩

private theorem vh_writeAddConstAt {w off addOff base : ℕ} {s : Memory.State}
    (ha : base + off < s.frontier) (hv : Fits w (base + addOff)) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (writeAddConstAtProg off addOff base)) :=
  ⟨⟨ha, hv⟩, trivial⟩

private theorem validHistory_initRootStaticA {c U V w base : ℕ} {s : Memory.State}
    (hw11 : 11 ≤ w) (hU0 : 0 < U) (hUw : U < 2 ^ w) (hV0 : 0 < V) (hVw : V ≤ 2 ^ w)
    (hb : base + 32 ≤ s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (initRootStaticAProg c U V w base)) := by
  obtain ⟨fU, fV, fw, _, fkb, _, fvb, _, _, fth, fct, _, _⟩ :=
    static_hdr_fits (c := c) hw11 hU0 hUw hV0 hVw
  unfold initRootStaticAProg hdrU1 hdrV1 hdrW hdrKeyBits hdrValBits hdrThresh hdrCTab
  refine vh_seqUnit (vh_writeConstAt (by omega) fU) ?_
  refine vh_seqUnit
    (vh_writeConstAt (by (repeat rw [cstate_writeConstAt]); dsimp only; omega) fV) ?_
  refine vh_seqUnit
    (vh_writeConstAt (by (repeat rw [cstate_writeConstAt]); dsimp only; omega) fw) ?_
  refine vh_seqUnit
    (vh_writeConstAt (by (repeat rw [cstate_writeConstAt]); dsimp only; omega) fkb) ?_
  refine vh_seqUnit
    (vh_writeConstAt (by (repeat rw [cstate_writeConstAt]); dsimp only; omega) fvb) ?_
  refine vh_seqUnit
    (vh_writeConstAt (by (repeat rw [cstate_writeConstAt]); dsimp only; omega) fth) ?_
  exact vh_writeConstAt (by (repeat rw [cstate_writeConstAt]); dsimp only; omega) fct

private theorem validHistory_initRootStaticB {c U w base : ℕ} {s : Memory.State}
    (hw11 : 11 ≤ w) (hU0 : 0 < U) (hUw : U < 2 ^ w) (hb : base + 194 ≤ s.frontier)
    (hwf : Memory.WellFormed w s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (initRootStaticBProg c U base)) := by
  obtain ⟨_, _, _, _, fkb, _, _, _, frw, _, _, fdt, fce⟩ :=
    static_hdr_fits (c := c) (V := 1) hw11 hU0 hUw Nat.one_pos Nat.one_le_two_pow
  have hfr_w := hwf.1
  have fib : Fits w (base + 192) := by dsimp only [Fits] at hfr_w ⊢; omega
  unfold initRootStaticBProg hdrDTab hdrRedW hdrCEff hdrItemLo hdrItemHi hdrQLo hdrQHi
  refine vh_seqUnit (vh_writeConstAt (by omega) fdt) ?_
  refine vh_seqUnit
    (vh_writeConstAt (by (repeat rw [cstate_writeConstAt]); dsimp only; omega) frw) ?_
  refine vh_seqUnit
    (vh_writeConstAt (by (repeat rw [cstate_writeConstAt]); dsimp only; omega) fce) ?_
  refine vh_seqUnit (vh_writeAddConstAt
    (by (repeat rw [cstate_writeConstAt]); dsimp only; omega) fib) ?_
  refine vh_seqUnit (vh_writeAddConstAt
    (by (repeat rw [cstate_writeConstAt]); (repeat rw [cstate_writeAddConstAt]); dsimp only; omega)
    fib) ?_
  refine vh_seqUnit (vh_writeConstAt
    (by (repeat rw [cstate_writeConstAt]); (repeat rw [cstate_writeAddConstAt]); dsimp only; omega)
    fkb) ?_
  exact vh_writeConstAt
    (by (repeat rw [cstate_writeConstAt]); (repeat rw [cstate_writeAddConstAt]); dsimp only; omega)
    fkb

private theorem writeSmallConstA_fr (offP offM kb base : ℕ) (s : Memory.State) :
    ((Memory.spec 0).clientState s (writeSmallConstAProg offP offM kb base)).frontier =
      s.frontier := by
  unfold writeSmallConstAProg
  repeat rw [cstate_seqUnit]
  repeat (first | rw [cstate_writeConstAt] | rw [cstate_writeAddConstAt])

private theorem writeSmallConstB_fr (offP wv vb kb base : ℕ) (s : Memory.State) :
    ((Memory.spec 0).clientState s (writeSmallConstBProg offP wv vb kb base)).frontier =
      s.frontier := by
  unfold writeSmallConstBProg
  repeat rw [cstate_seqUnit]
  repeat (first | rw [cstate_writeConstAt] | rw [cstate_writeAddConstAt])

private theorem writeSmallConst_fr (offP offM wv vb kb base : ℕ) (s : Memory.State) :
    ((Memory.spec 0).clientState s (writeSmallConstProg offP offM wv vb kb base)).frontier =
      s.frontier := by
  unfold writeSmallConstProg
  rw [cstate_seqUnit, writeSmallConstB_fr, writeSmallConstA_fr]

private theorem realizesBounded_writeSmallConstA (offP offM kb : ℕ) :
    RealizesBounded .exact (writeSmallConstAProg offP offM kb)
      (WordEncoding.encode (α := ℕ)) (WordEncoding.encode (α := Unit))
      (fun w base s =>
        8 ≤ w ∧ offP ≤ 128 ∧ Fits w offM ∧ Fits w kb ∧
        base + 194 ≤ s.frontier ∧ base + offP + 61 ≤ s.frontier ∧ base + offM < s.frontier)
      (fun _ _ => 0) :=
  (realizesBounded_seqUnit (realizesBounded_writeConstAt offP 0) <|
   realizesBounded_seqUnit (realizesBounded_writeAddConstAt (offP + 1) offM) <|
   realizesBounded_seqUnit (realizesBounded_writeConstAt (offP + 48) 0) <|
   realizesBounded_seqUnit (realizesBounded_writeConstAt (offP + 49) 0) <|
   realizesBounded_seqUnit (realizesBounded_writeAddConstAt (offP + 50) hdrSplit) <|
   realizesBounded_seqUnit (realizesBounded_writeAddConstAt (offP + 51) 192) <|
   realizesBounded_seqUnit (realizesBounded_writeConstAt (offP + 52) kb)
     (realizesBounded_writeConstAt (offP + 53) 1)).consequence
    (fun w base s _ _ ⟨hw8, hoP, fM, fkb, hb194, hop, hom⟩ => by
      have h256 : 256 ≤ 2 ^ w :=
        (by decide : 256 = 2 ^ 8) ▸ Nat.pow_le_pow_right (by decide) hw8
      repeat (first | rw [cstate_writeConstAt] | rw [cstate_writeAddConstAt])
      dsimp only [hdrSplit, Fits] at *
      exact ⟨⟨by omega, by omega, by omega⟩, ⟨by omega, fM, by omega, by omega⟩,
        ⟨by omega, by omega, by omega⟩, ⟨by omega, by omega, by omega⟩,
        ⟨by omega, by omega, by omega, by omega⟩, ⟨by omega, by omega, by omega, by omega⟩,
        ⟨by omega, fkb, by omega⟩, ⟨by omega, by omega, by omega⟩⟩)
    (fun _ _ => le_rfl)

private theorem realizesBounded_writeSmallConstB (offP wv vb kb : ℕ) :
    RealizesBounded .exact (writeSmallConstBProg offP wv vb kb)
      (WordEncoding.encode (α := ℕ)) (WordEncoding.encode (α := Unit))
      (fun w base s =>
        8 ≤ w ∧ offP ≤ 128 ∧ Fits w wv ∧ Fits w vb ∧ Fits w kb ∧
        base + 194 ≤ s.frontier ∧ base + offP + 61 ≤ s.frontier)
      (fun _ _ => 0) :=
  (realizesBounded_seqUnit (realizesBounded_writeConstAt (offP + 54) wv) <|
   realizesBounded_seqUnit (realizesBounded_writeConstAt (offP + 55) 32) <|
   realizesBounded_seqUnit (realizesBounded_writeConstAt (offP + 56) 4) <|
   realizesBounded_seqUnit (realizesBounded_writeAddConstAt (offP + 57) 192) <|
   realizesBounded_seqUnit (realizesBounded_writeConstAt (offP + 58) kb) <|
   realizesBounded_seqUnit (realizesBounded_writeConstAt (offP + 59) vb)
     (realizesBounded_writeConstAt (offP + 60) 0)).consequence
    (fun w base s _ _ ⟨hw8, hoP, fwv, fvb, fkb, hb194, hop⟩ => by
      have h256 : 256 ≤ 2 ^ w :=
        (by decide : 256 = 2 ^ 8) ▸ Nat.pow_le_pow_right (by decide) hw8
      repeat (first | rw [cstate_writeConstAt] | rw [cstate_writeAddConstAt])
      dsimp only [Fits] at *
      exact ⟨⟨by omega, fwv, by omega⟩, ⟨by omega, by omega, by omega⟩,
        ⟨by omega, by omega, by omega⟩, ⟨by omega, by omega, by omega, by omega⟩,
        ⟨by omega, fkb, by omega⟩, ⟨by omega, fvb, by omega⟩,
        ⟨by omega, by omega, by omega⟩⟩)
    (fun _ _ => le_rfl)

private theorem realizesBounded_writeSmallConst (offP offM wv vb kb : ℕ) :
    RealizesBounded .exact (writeSmallConstProg offP offM wv vb kb)
      (WordEncoding.encode (α := ℕ)) (WordEncoding.encode (α := Unit))
      (fun w base s =>
        8 ≤ w ∧ offP ≤ 128 ∧ Fits w offM ∧ Fits w wv ∧ Fits w vb ∧ Fits w kb ∧
        base + 194 ≤ s.frontier ∧ base + offP + 61 ≤ s.frontier ∧ base + offM < s.frontier)
      (fun _ _ => 0) :=
  (realizesBounded_seqUnit
    (realizesBounded_writeSmallConstA offP offM kb)
    (realizesBounded_writeSmallConstB offP wv vb kb)).consequence
    (fun _ base s _ _ ⟨hw8, hoP, fM, fwv, fvb, fkb, hb194, hop, hom⟩ => by
      rw [writeSmallConstA_fr]
      exact ⟨⟨hw8, hoP, fM, fkb, hb194, hop, hom⟩, ⟨hw8, hoP, fwv, fvb, fkb, hb194, hop⟩⟩)
    (fun _ _ => le_rfl)

private theorem validHistory_writeSmallConstA {w offP offM kb base : ℕ} {s : Memory.State}
    (hw8 : 8 ≤ w) (fkb : Fits w kb)
    (hb194 : base + 194 ≤ s.frontier) (hop : base + offP + 61 ≤ s.frontier)
    (hom : base + offM < s.frontier) (hwf : Memory.WellFormed w s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (writeSmallConstAProg offP offM kb base)) := by
  have h256 : 256 ≤ 2 ^ w :=
    (by decide : 256 = 2 ^ 8) ▸ Nat.pow_le_pow_right (by decide) hw8
  have hfr_w := hwf.1
  have hz : Fits w 0 := Nat.two_pow_pos w
  have f1 : Fits w 1 := by dsimp only [Fits]; omega
  have fm : Fits w (base + offM) := by dsimp only [Fits] at hfr_w ⊢; omega
  have fsp : Fits w (base + hdrSplit) := by unfold hdrSplit; dsimp only [Fits] at hfr_w ⊢; omega
  have fib : Fits w (base + 192) := by dsimp only [Fits] at hfr_w ⊢; omega
  unfold writeSmallConstAProg
  refine vh_seqUnit (vh_writeConstAt (by omega) hz) ?_
  rw [cstate_writeConstAt]
  refine vh_seqUnit (vh_writeAddConstAt (by dsimp only; omega) fm) ?_
  rw [cstate_writeAddConstAt]
  refine vh_seqUnit (vh_writeConstAt (by dsimp only; omega) hz) ?_
  rw [cstate_writeConstAt]
  refine vh_seqUnit (vh_writeConstAt (by dsimp only; omega) hz) ?_
  rw [cstate_writeConstAt]
  refine vh_seqUnit (vh_writeAddConstAt (by dsimp only; omega) fsp) ?_
  rw [cstate_writeAddConstAt]
  refine vh_seqUnit (vh_writeAddConstAt (by dsimp only; omega) fib) ?_
  rw [cstate_writeAddConstAt]
  refine vh_seqUnit (vh_writeConstAt (by dsimp only; omega) fkb) ?_
  rw [cstate_writeConstAt]
  exact vh_writeConstAt (by dsimp only; omega) f1

private theorem validHistory_writeSmallConstB {w offP wv vb kb base : ℕ} {s : Memory.State}
    (hw8 : 8 ≤ w) (fwv : Fits w wv) (fvb : Fits w vb) (fkb : Fits w kb)
    (hb194 : base + 194 ≤ s.frontier) (hop : base + offP + 61 ≤ s.frontier)
    (hwf : Memory.WellFormed w s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (writeSmallConstBProg offP wv vb kb base)) := by
  have h256 : 256 ≤ 2 ^ w :=
    (by decide : 256 = 2 ^ 8) ▸ Nat.pow_le_pow_right (by decide) hw8
  have hfr_w := hwf.1
  have hz : Fits w 0 := Nat.two_pow_pos w
  have f4 : Fits w 4 := by dsimp only [Fits]; omega
  have f32 : Fits w 32 := by dsimp only [Fits]; omega
  have fib : Fits w (base + 192) := by dsimp only [Fits] at hfr_w ⊢; omega
  unfold writeSmallConstBProg
  refine vh_seqUnit (vh_writeConstAt (by omega) fwv) ?_
  rw [cstate_writeConstAt]
  refine vh_seqUnit (vh_writeConstAt (by dsimp only; omega) f32) ?_
  rw [cstate_writeConstAt]
  refine vh_seqUnit (vh_writeConstAt (by dsimp only; omega) f4) ?_
  rw [cstate_writeConstAt]
  refine vh_seqUnit (vh_writeAddConstAt (by dsimp only; omega) fib) ?_
  rw [cstate_writeAddConstAt]
  refine vh_seqUnit (vh_writeConstAt (by dsimp only; omega) fkb) ?_
  rw [cstate_writeConstAt]
  refine vh_seqUnit (vh_writeConstAt (by dsimp only; omega) fvb) ?_
  rw [cstate_writeConstAt]
  exact vh_writeConstAt (by dsimp only; omega) hz

private theorem validHistory_writeSmallConst {w offP offM wv vb kb base : ℕ} {s : Memory.State}
    (hw8 : 8 ≤ w) (fwv : Fits w wv) (fvb : Fits w vb) (fkb : Fits w kb)
    (hb194 : base + 194 ≤ s.frontier) (hop : base + offP + 61 ≤ s.frontier)
    (hom : base + offM < s.frontier) (hwf : Memory.WellFormed w s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (writeSmallConstProg offP offM wv vb kb base)) := by
  have vha := validHistory_writeSmallConstA (offP := offP) (offM := offM)
    hw8 fkb hb194 hop hom hwf
  refine vh_seqUnit vha ?_
  have hwf1 := wf_step hwf vha
  have hfr1 := writeSmallConstA_fr offP offM kb base s
  exact validHistory_writeSmallConstB hw8 fwv fvb fkb
    (by rw [hfr1]; exact hb194) (by rw [hfr1]; exact hop) hwf1

/-- `RealizesBounded .exact` (`¬ReadsWidth`) initializer populating the 192-word dual-epoch root
header and dual small `ParamTable`s on a freshly zeroed `[base, base + 194)` arena. -/
def initDualRootProg (c U V w : ℕ) : ℕ → Memory.Prog Unit :=
  seqUnit (initRootStaticAProg c U V w) <|
  seqUnit (initRootStaticBProg c U) <|
  seqUnit (writeSmallConstProg hdrPBase0 hdrSmallMeta0 w (initValBitsVal V) (initKeyBitsVal U))
    (writeSmallConstProg hdrPBase1 hdrSmallMeta1 w (initValBitsVal V) (initKeyBitsVal U))

private theorem writeSmallConstA_spec (offP offM kb base : ℕ) (s : Memory.State) :
    let sA := (Memory.spec 0).clientState s (writeSmallConstAProg offP offM kb base)
    sA.mem (base + offP) = 0 ∧
    sA.mem (base + offP + 1) = base + offM ∧
    sA.mem (base + offP + 48) = 0 ∧
    sA.mem (base + offP + 49) = 0 ∧
    sA.mem (base + offP + 50) = base + hdrSplit ∧
    sA.mem (base + offP + 51) = base + 192 ∧
    sA.mem (base + offP + 52) = kb ∧
    sA.mem (base + offP + 53) = 1 ∧
    (∀ addr, ¬(base + offP ≤ addr ∧ addr < base + offP + 54) → sA.mem addr = s.mem addr) := by
  dsimp only
  unfold writeSmallConstAProg
  repeat rw [cstate_seqUnit]
  repeat (first | rw [cstate_writeConstAt] | rw [cstate_writeAddConstAt])
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun addr ha => ?_⟩
  · iterate 7 rw [Function.update_of_ne (by omega)]
    exact Function.update_self ..
  · iterate 6 rw [Function.update_of_ne (by omega)]
    rw [show base + offP + 1 = base + (offP + 1) by omega]; exact Function.update_self ..
  · iterate 5 rw [Function.update_of_ne (by omega)]
    rw [show base + offP + 48 = base + (offP + 48) by omega]; exact Function.update_self ..
  · iterate 4 rw [Function.update_of_ne (by omega)]
    rw [show base + offP + 49 = base + (offP + 49) by omega]; exact Function.update_self ..
  · iterate 3 rw [Function.update_of_ne (by omega)]
    rw [show base + offP + 50 = base + (offP + 50) by omega]; exact Function.update_self ..
  · iterate 2 rw [Function.update_of_ne (by omega)]
    rw [show base + offP + 51 = base + (offP + 51) by omega]; exact Function.update_self ..
  · rw [Function.update_of_ne (by omega)]
    rw [show base + offP + 52 = base + (offP + 52) by omega]; exact Function.update_self ..
  · rw [show base + offP + 53 = base + (offP + 53) by omega]; exact Function.update_self ..
  · iterate 8 rw [Function.update_of_ne (by omega)]

private theorem writeSmallConstB_spec (offP wv vb kb base : ℕ) (s : Memory.State) :
    let sB := (Memory.spec 0).clientState s (writeSmallConstBProg offP wv vb kb base)
    sB.mem (base + offP + 54) = wv ∧
    sB.mem (base + offP + 55) = 32 ∧
    sB.mem (base + offP + 56) = 4 ∧
    sB.mem (base + offP + 57) = base + 192 ∧
    sB.mem (base + offP + 58) = kb ∧
    sB.mem (base + offP + 59) = vb ∧
    sB.mem (base + offP + 60) = 0 ∧
    (∀ addr, ¬(base + offP + 54 ≤ addr ∧ addr < base + offP + 61) → sB.mem addr = s.mem addr) := by
  dsimp only
  unfold writeSmallConstBProg
  repeat rw [cstate_seqUnit]
  repeat (first | rw [cstate_writeConstAt] | rw [cstate_writeAddConstAt])
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun addr ha => ?_⟩
  · iterate 6 rw [Function.update_of_ne (by omega)]
    rw [show base + offP + 54 = base + (offP + 54) by omega]; exact Function.update_self ..
  · iterate 5 rw [Function.update_of_ne (by omega)]
    rw [show base + offP + 55 = base + (offP + 55) by omega]; exact Function.update_self ..
  · iterate 4 rw [Function.update_of_ne (by omega)]
    rw [show base + offP + 56 = base + (offP + 56) by omega]; exact Function.update_self ..
  · iterate 3 rw [Function.update_of_ne (by omega)]
    rw [show base + offP + 57 = base + (offP + 57) by omega]; exact Function.update_self ..
  · iterate 2 rw [Function.update_of_ne (by omega)]
    rw [show base + offP + 58 = base + (offP + 58) by omega]; exact Function.update_self ..
  · rw [Function.update_of_ne (by omega)]
    rw [show base + offP + 59 = base + (offP + 59) by omega]; exact Function.update_self ..
  · rw [show base + offP + 60 = base + (offP + 60) by omega]; exact Function.update_self ..
  · iterate 7 rw [Function.update_of_ne (by omega)]

private theorem writeSmallConst_spec (U V offP offM wv vb kb base : ℕ) (s : Memory.State) :
    let s' := (Memory.spec 0).clientState s (writeSmallConstProg offP offM wv vb kb base)
    let L : SmallEpochLayout := ⟨base + offM, U, V, directSlotIo wv vb base (base + 192) kb 0⟩
    s'.frontier = s.frontier ∧
    memoryCost (writeSmallConstProg offP offM wv vb kb base) s = 15 ∧
    L.ParamTable (base + offP) s'.mem ∧
    (∀ addr, ¬(base + offP ≤ addr ∧ addr < base + offP + 61) → s'.mem addr = s.mem addr) := by
  dsimp only
  have hst : (Memory.spec 0).clientState s (writeSmallConstProg offP offM wv vb kb base) =
      (Memory.spec 0).clientState
        ((Memory.spec 0).clientState s (writeSmallConstAProg offP offM kb base))
        (writeSmallConstBProg offP wv vb kb base) := cstate_seqUnit ..
  have hA := writeSmallConstA_spec offP offM kb base s
  have hB := writeSmallConstB_spec offP wv vb kb base
    ((Memory.spec 0).clientState s (writeSmallConstAProg offP offM kb base))
  refine ⟨writeSmallConst_fr offP offM wv vb kb base s, ?_, ?_, fun addr ha => ?_⟩
  · unfold writeSmallConstProg writeSmallConstAProg writeSmallConstBProg
    simp only [mcost_seqUnit, mcost_writeConstAt, mcost_writeAddConstAt]
  · rw [hst]
    unfold SmallEpochLayout.ParamTable directSlotIo
    dsimp only
    exact ⟨(hB.2.2.2.2.2.2.2 _ (by omega)).trans hA.1,
      (hB.2.2.2.2.2.2.2 _ (by omega)).trans hA.2.1,
      (hB.2.2.2.2.2.2.2 _ (by omega)).trans hA.2.2.1,
      (hB.2.2.2.2.2.2.2 _ (by omega)).trans hA.2.2.2.1,
      (hB.2.2.2.2.2.2.2 _ (by omega)).trans hA.2.2.2.2.1,
      (hB.2.2.2.2.2.2.2 _ (by omega)).trans hA.2.2.2.2.2.1,
      (hB.2.2.2.2.2.2.2 _ (by omega)).trans hA.2.2.2.2.2.2.1,
      (hB.2.2.2.2.2.2.2 _ (by omega)).trans hA.2.2.2.2.2.2.2.1,
      hB.1, hB.2.1, hB.2.2.1, hB.2.2.2.1, hB.2.2.2.2.1, hB.2.2.2.2.2.1, hB.2.2.2.2.2.2.1⟩
  · rw [hst]
    exact (hB.2.2.2.2.2.2.2 addr (by omega)).trans (hA.2.2.2.2.2.2.2.2 addr (by omega))

theorem realizesBounded_initDualRoot (c U V w_p : ℕ) :
    RealizesBounded .exact (initDualRootProg c U V w_p)
      (WordEncoding.encode (α := ℕ)) (WordEncoding.encode (α := Unit))
      (fun w base s =>
        w = w_p ∧ 11 ≤ w ∧ 0 < U ∧ U < 2 ^ w ∧ 0 < V ∧ V ≤ 2 ^ w ∧ base + 194 ≤ s.frontier)
      (fun _ _ => 0) :=
  (realizesBounded_seqUnit (realizesBounded_initRootStaticA c U V w_p) <|
   realizesBounded_seqUnit (realizesBounded_initRootStaticB c U) <|
   realizesBounded_seqUnit
     (realizesBounded_writeSmallConst hdrPBase0 hdrSmallMeta0 w_p
       (initValBitsVal V) (initKeyBitsVal U))
     (realizesBounded_writeSmallConst hdrPBase1 hdrSmallMeta1 w_p
       (initValBitsVal V) (initKeyBitsVal U))).consequence
    (fun w base s _ _ ⟨rfl, hw11, hU0, hUw, hV0, hVw, hfr⟩ => by
      obtain ⟨_, _, fw, _, fkb, _, fvb, _, _, _, _, _, _⟩ :=
        static_hdr_fits (c := c) hw11 hU0 hUw hV0 hVw
      have h2w : 2048 ≤ 2 ^ w :=
        (by decide : 2048 = 2 ^ 11) ▸ Nat.pow_le_pow_right (by decide) hw11
      repeat (first | rw [writeSmallConst_fr] | rw [initRootStaticB_fr] | rw [initRootStaticA_fr])
      dsimp only [hdrPBase0, hdrPBase1, hdrSmallMeta0, hdrSmallMeta1, Fits] at *
      exact ⟨⟨rfl, hw11, hU0, hUw, hV0, hVw, by omega⟩,
        ⟨hw11, hU0, hUw, hfr⟩,
        ⟨by omega, by omega, by omega, fw, fvb, fkb, hfr, by omega, by omega⟩,
        ⟨by omega, by omega, by omega, fw, fvb, fkb, hfr, by omega, by omega⟩⟩)
    (fun _ _ => le_rfl)

theorem validHistory_initDualRootProg {c U V w base : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s)
    (hw11 : 11 ≤ w) (hU0 : 0 < U) (hUw : U < 2 ^ w) (hV0 : 0 < V) (hVw : V ≤ 2 ^ w)
    (hb : base + 194 ≤ s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (initDualRootProg c U V w base)) := by
  obtain ⟨_, _, fw, _, fkb, _, fvb, _, _, _, _, _, _⟩ :=
    static_hdr_fits (c := c) hw11 hU0 hUw hV0 hVw
  unfold initDualRootProg
  have vha := validHistory_initRootStaticA (s := s) (c := c) (base := base)
    hw11 hU0 hUw hV0 hVw (by omega)
  refine vh_seqUnit vha ?_
  set s1 := (Memory.spec 0).clientState s (initRootStaticAProg c U V w base)
  have hwf1 : Memory.WellFormed w s1 := wf_step hwf vha
  have hfr1 : s1.frontier = s.frontier := initRootStaticA_fr c U V w base s
  have vhb := validHistory_initRootStaticB (c := c) (s := s1) hw11 hU0 hUw
    (by rw [hfr1]; omega) hwf1
  refine vh_seqUnit vhb ?_
  set s2 := (Memory.spec 0).clientState s1 (initRootStaticBProg c U base)
  have hwf2 : Memory.WellFormed w s2 := wf_step hwf1 vhb
  have hfr2 : s2.frontier = s.frontier := (initRootStaticB_fr c U base s1).trans hfr1
  have vhw0 := validHistory_writeSmallConst (offP := hdrPBase0) (offM := hdrSmallMeta0)
    (s := s2) (by omega) fw fvb fkb (by rw [hfr2]; omega)
    (by rw [hfr2]; unfold hdrPBase0; omega) (by rw [hfr2]; unfold hdrSmallMeta0; omega) hwf2
  refine vh_seqUnit vhw0 ?_
  set s3 := (Memory.spec 0).clientState s2
    (writeSmallConstProg hdrPBase0 hdrSmallMeta0 w (initValBitsVal V) (initKeyBitsVal U) base)
  have hwf3 : Memory.WellFormed w s3 := wf_step hwf2 vhw0
  have hfr3 : s3.frontier = s.frontier :=
    (writeSmallConst_fr _ _ _ _ _ base s2).trans hfr2
  exact validHistory_writeSmallConst (offP := hdrPBase1) (offM := hdrSmallMeta1)
    (s := s3) (by omega) fw fvb fkb (by rw [hfr3]; omega)
    (by rw [hfr3]; unfold hdrPBase1; omega) (by rw [hfr3]; unfold hdrSmallMeta1; omega) hwf3

/-! ## Section 5: `remRebuildBudget`, `DualLatent`, `DualStateInv`, `DualMidInv`, and Foreground
Operations -/

/-- Upper bound on ticks of one stage (`4..9`: `zeroMeta` + `randFill` + `initDir` + `initTail` +
`migrate` + `unperm`) relative to `nRef = max (whpThreshold c) nSrc`. -/
@[expose] def maxStageBudget (nRef : ℕ) : ℕ :=
  let pgRef := max 32 (Nat.log 2 (2 * nRef) + 4)
  3 * ((2 * nRef + 512) / 1024 + 3) +
    ((nRef / 16 + 16) / 1024 + 2) +
    ((8 * pgRef) / 128 + 2) +
    (nRef / 240 + pgRef / 8 + 6)

/-- Upper bound on ticks of tail phases `10` (`slideDown`) and `11` (`shrinkPost`) plus `+ 2`
safety margin. -/
@[expose] def maxTailPhasesBudget (nRef : ℕ) : ℕ :=
  ((2 * nRef + 512) / 1023 + 2) + ((9 * nRef) / 1022 + 4)

/-- Total initial tick budget for a full 2-stage rebuild (`1..11`), bounded by `nRef / 16`. -/
@[expose] def totalRebuildBudget (nRef : ℕ) : ℕ :=
  (2 * Nat.log 2 (2 * nRef) + 8) +
    ((9 * nRef) / 1022 + 2) +
    ((2 * nRef + 512) / 1024 + 2) +
    2 * maxStageBudget nRef +
    maxTailPhasesBudget nRef

theorem totalRebuildBudget_mul16_le {nRef : ℕ} (hN : 2 ^ 20 ≤ nRef) :
    16 * totalRebuildBudget nRef ≤ nRef := by
  have hlog := log_add_two_le_div_1024 hN
  have hlog2 : Nat.log 2 (2 * nRef) ≤ Nat.log 2 nRef + 1 := by
    rw [Nat.mul_comm 2, Nat.log_mul_base Nat.one_lt_two (by omega)]
  unfold totalRebuildBudget maxStageBudget maxTailPhasesBudget
  dsimp only [Nat.max_def]
  split_ifs <;> omega

/-- Remaining ticks strictly after the current `(stg, ph)` sub-phase. -/
@[expose] def futureRebuildBudget (nRef stg ph : ℕ) : ℕ :=
  let pgRef := max 32 (Nat.log 2 (2 * nRef) + 4)
  let _bZero := (2 * nRef + 512) / 1024 + 3
  let bRand := (2 * nRef + 512) / 1024 + 3
  let bDir := (nRef / 16 + 16) / 1024 + 2
  let bTail := (8 * pgRef) / 128 + 2
  let bMig := (2 * nRef + 512) / 1024 + 3
  let bUnp := nRef / 240 + pgRef / 8 + 6
  let stageRem :=
    if ph = 4 then bRand + bDir + bTail + bMig + bUnp
    else if ph = 5 then bDir + bTail + bMig + bUnp
    else if ph = 6 then bTail + bMig + bUnp
    else if ph = 7 then bMig + bUnp
    else if ph = 8 then bUnp
    else 0
  if ph = 1 then
    ((9 * nRef) / 1022 + 2) + ((2 * nRef + 512) / 1024 + 2) +
      2 * maxStageBudget nRef + maxTailPhasesBudget nRef
  else if ph = 2 then
    ((2 * nRef + 512) / 1024 + 2) + 2 * maxStageBudget nRef + maxTailPhasesBudget nRef
  else if ph = 3 then
    2 * maxStageBudget nRef + maxTailPhasesBudget nRef
  else if 4 ≤ ph ∧ ph ≤ 9 then
    stageRem + (if stg = 0 then maxStageBudget nRef else 0) + maxTailPhasesBudget nRef
  else if ph = 10 then
    (9 * nRef) / 1022 + 4
  else
    0

/-- Exact countdown tick budget for the active `(stg, ph)` rebuild state (`≥ 2` for `1 ≤ ph ≤ 11`).
-/
@[expose] def remRebuildBudget (nRef stg ph logSub logK growDiff sp slideRem mDst offBM maxPg
    pgHost cur rem shrinkDiff : ℕ) : ℕ :=
  let curRem :=
    if ph = 1 then
      if logSub = 0 then (Nat.log 2 (2 * nRef) + 2 - logK) + (Nat.log 2 (2 * nRef) + 3) + 1
      else if logSub = 1 then (Nat.log 2 (2 * nRef) + 2 - logK) + 1
      else 1
    else if ph = 2 then growDiff / 1022 + 1
    else if ph = 3 then sp / 1024 + 1
    else if ph = 4 then (mDst - cur) / 1024 + 1
    else if ph = 5 then (offBM - cur) / 1024 + 1
    else if ph = 6 then (maxPg - cur) / 1024 + 1
    else if ph = 7 then (8 * pgHost - cur) / 128 + 1
    else if ph = 8 then rem
    else if ph = 9 then rem
    else if ph = 10 then slideRem / 1023 + 1
    else shrinkDiff / 1022 + 2
  curRem + futureRebuildBudget nRef stg ph

/-- Latent logical, schedule, and probabilistic state of the 2-slot dual-epoch dictionary. -/
structure DualLatent (c U V : ℕ) where
  /-- Source/primary slot (`slot 0` in `ph ≤ 3`, `pSrc` in `ph ∈ {4..8}`). -/
  slotSrc : SlotLatent c U V
  /-- Destination slot (`pDst` in `ph ∈ {6..9}`, `slot 0` in `ph ∈ {10, 11}`). -/
  slotDst : SlotLatent c U V
  /-- Live item count `nTrig` at the operation that triggered the active rebuild (`1 ≤ ph`). -/
  nTrig : ℕ
  /-- `epochOps` value at trigger time (`dualTriggerCap c U nSrc nTrig trigOps = some nDst`). -/
  trigOps : ℕ
  /-- Number of background ticks elapsed since the active rebuild started (`0` in `ph = 0`). -/
  elapsed : ℕ
  /-- Deterministic upper bound on `PageUnpermState.unpermRank` during `ph = 9` (`unperm`). -/
  unpermBound : ℕ

/-- Canonical active `SlotIoLayout` of the primary/source slot (`ph ≤ 8`). -/
@[expose] def activeSrcIo (c w vB base stg ph nSrc nDst pad ibLo qLo ibHi qHi nc : ℕ) :
    SlotIoLayout :=
  if ph < 3 then directSlotIo w vB base ibLo qLo nc
  else if ph = 3 then splitSlotIo w vB base ibLo qLo ibHi qHi nc
  else if ph < 8 then directSlotIo w vB base ibHi qHi nc
  else
    let nHost := if nDst = 0 then nSrc else nDst
    let mbHost := if nDst = 0 then base + 192
      else if stg = 0 then base + 192 + pad else base + 192
    pagedSlotIo 0 (hostPageLayout c w nHost mbHost ibHi qHi vB nc)

/-- Canonical active `SlotIoLayout` of the destination slot (`6 ≤ ph ≤ 11`). -/
@[expose] def activeDstIo (c w vB base stg ph nSrc nDst pad ibLo qLo ibHi qHi nc unpermDone : ℕ) :
    SlotIoLayout :=
  let nHost := if nDst = 0 then nSrc else nDst
  let mbHost := if nDst = 0 then base + 192
    else if stg = 0 then base + 192 + pad else base + 192
  if ph < 8 then directSlotIo w vB base ibHi qHi nc
  else if ph = 8 then pagedSlotIo 1 (hostPageLayout c w nHost mbHost ibHi qHi vB nc)
  else if ph = 9 then
    if unpermDone = 0 then pagedSlotIo 1 (hostPageLayout c w nHost mbHost ibHi qHi vB nc)
    else directSlotIo w vB base ibHi qHi nc
  else if ph = 10 then splitSlotIo w vB base ibLo qLo ibHi qHi nc
  else directSlotIo w vB base ibLo qLo nc

/-- Cached 5-word page-host offset block (`38..42` for `nSrc`, `43..47` for `nDst`). -/
@[expose] def HostCacheValid (c w N off0 base : ℕ) (mem : ℕ → ℕ) : Prop :=
  0 < N →
    mem (base + off0) = offPageDir c w N ∧
    mem (base + off0 + 1) = offPageTail c w N ∧
    mem (base + off0 + 2) = globalPtrBits N ∧
    mem (base + off0 + 3) = pageSizeWhp N ∧
    mem (base + off0 + 4) = N / pageSizeWhp N + 4

/-- Active source-slot capacity `if stg = 0 then nSrc else nDst`. -/
abbrev dualCapSrc (base : ℕ) (mem : ℕ → ℕ) : ℕ :=
  if mem (base + hdrStage) = 0 then mem (base + hdrNSrc) else mem (base + hdrNDst)

/-- Active source-slot metadata base address. -/
abbrev dualMbSrc (base : ℕ) (mem : ℕ → ℕ) : ℕ :=
  if mem (base + hdrStage) = 0 then
    if mem (base + hdrNSrc) = 0 then base + hdrSmallMeta0 else base + 192
  else base + 192 + mem (base + hdrPad)

/-- Active source-slot parameter-table base address. -/
abbrev dualPSrc (base : ℕ) (mem : ℕ → ℕ) : ℕ :=
  if mem (base + hdrStage) = 0 then base + hdrPBase0 else base + hdrPBase1

/-- Active destination-slot metadata base address. -/
abbrev dualMbDst (base : ℕ) (mem : ℕ → ℕ) : ℕ :=
  if mem (base + hdrPhase) < 10 then
    if mem (base + hdrNDst) = 0 then base + hdrSmallMeta1
    else if mem (base + hdrStage) = 0 then base + 192 + mem (base + hdrPad) else base + 192
  else
    if mem (base + hdrNDst) = 0 then base + hdrSmallMeta0 else base + 192

/-- Active destination-slot parameter-table base address. -/
abbrev dualPDst (base : ℕ) (mem : ℕ → ℕ) : ℕ :=
  if mem (base + hdrPhase) < 10 then
    if mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0
  else base + hdrPBase0

/-- Shared page-arena host capacity `if nDst = 0 then nSrc else nDst`. -/
abbrev dualNHost (base : ℕ) (mem : ℕ → ℕ) : ℕ :=
  if mem (base + hdrNDst) = 0 then mem (base + hdrNSrc) else mem (base + hdrNDst)

/-- Shared page-arena host metadata base address. -/
abbrev dualMbHost (base : ℕ) (mem : ℕ → ℕ) : ℕ :=
  if mem (base + hdrNDst) = 0 then base + 192
  else if mem (base + hdrStage) = 0 then base + 192 + mem (base + hdrPad) else base + 192

/-- Shared page-arena `PageArenaLayout` at capacity `nc`. -/
abbrev dualPgHost (c V w base nc : ℕ) (mem : ℕ → ℕ) : PageArenaLayout :=
  hostPageLayout c w (dualNHost base mem) (dualMbHost base mem)
    (mem (base + hdrItemHi)) (mem (base + hdrQHi)) (valBits V) nc

/-- `ParamTable`-masked memory map during Phase `5` (`randFill`) before `setDirectSlotIoProg`. -/
abbrev dualPh5MaskMem (V w base pDst ibHi qHi nLive : ℕ) (mem : ℕ → ℕ) : ℕ → ℕ :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update mem
      (pDst + 48) 0) (pDst + 49) 0) (pDst + 50) (base + hdrSplit)) (pDst + 51) ibHi)
      (pDst + 52) qHi) (pDst + 53) 1) (pDst + 54) w) (pDst + 55) 32) (pDst + 56) 4)
      (pDst + 57) ibHi) (pDst + 58) qHi) (pDst + 59) (valBits V)) (pDst + 60) nLive

/-- Idle (`ph = 0`) schedule, hysteresis, and frontier sub-invariant of `DualCoreInv`. -/
structure DualIdleSched (isMid : Bool) (c U V w base nLive : ℕ) (L : DualLatent c U V)
    (s : Memory.State) : Prop where
  /-- Stage is `0` when idle. -/
  stg_zero : s.mem (base + hdrStage) = 0
  /-- Destination capacity is `0` when idle. -/
  nDst_zero : s.mem (base + hdrNDst) = 0
  /-- Destination metadata size is `0` when idle. -/
  mDst_zero : s.mem (base + hdrMDst) = 0
  /-- Low item-stream base equals `base + 192 + mSrc`. -/
  ibLo_eq : s.mem (base + hdrItemLo) = base + 192 + s.mem (base + hdrMSrc)
  /-- High item-stream base equals `ibLo`. -/
  ibHi_eq : s.mem (base + hdrItemHi) = s.mem (base + hdrItemLo)
  /-- Low quotient width matches `nSrc`. -/
  qLo_eq :
    s.mem (base + hdrQLo) =
      (if s.mem (base + hdrNSrc) = 0 then keyBits U else quotBitsWhp U (s.mem (base + hdrNSrc)))
  /-- High quotient width equals `qLo`. -/
  qHi_eq : s.mem (base + hdrQHi) = s.mem (base + hdrQLo)
  /-- Elapsed rebuild ticks is `0` when idle. -/
  elapsed_zero : L.elapsed = 0
  /-- Resting (`DualIdleSafe`) or mid-step (`DualPostUpdateSafe`) hysteresis & frontier bounds. -/
  safe_fr :
    if isMid then
      DualPostUpdateSafe c U (s.mem (base + hdrNSrc)) nLive ∧
      s.frontier ≤ base + dualPaddedWords c U V w (s.mem (base + hdrNSrc))
        (s.mem (base + hdrNSrc)) nLive ∧
      s.mem (base + hdrItemLo) + pairStreamWords nLive (s.mem (base + hdrQLo)) (valBits V) w ≤
        s.frontier ∧
      s.frontier ≤
        s.mem (base + hdrItemLo) +
          pairStreamWords (nLive + 1) (s.mem (base + hdrQLo)) (valBits V) w
    else
      DualIdleSafe c U (s.mem (base + hdrNSrc)) nLive ∧
      (s.mem (base + hdrNSrc) = 0 → nLive < whpThreshold c) ∧
      s.frontier =
        s.mem (base + hdrItemLo) + pairStreamWords nLive (s.mem (base + hdrQLo)) (valBits V) w
  /-- Periodic rebuild counter & event-log conservation when `0 < nSrc`. -/
  ops_evs :
    0 < s.mem (base + hdrNSrc) →
      4 * s.mem (base + hdrEpochOps) < s.mem (base + hdrNSrc) + (if isMid then 4 else 0) ∧
      2 * L.slotSrc.evs.length ≤
        3 * s.mem (base + hdrNSrc) + 2 * s.mem (base + hdrEpochOps) + (if isMid then 2 else 0)

/-- Active rebuild (`1 ≤ ph ≤ 11`) schedule, frontier, and countdown budget sub-invariant. -/
structure DualActiveSched (isMid : Bool) (c U V w base nLive : ℕ) (L : DualLatent c U V)
    (s : Memory.State) : Prop where
  /-- Destination capacity is `0` or in `[whpThreshold c, U]`. -/
  nDst_bounds :
    s.mem (base + hdrNDst) = 0 ∨
      (whpThreshold c ≤ s.mem (base + hdrNDst) ∧ s.mem (base + hdrNDst) ≤ U)
  /-- Constraints when shrinking to small regime (`nDst = 0`). -/
  nDst_zero :
    s.mem (base + hdrNDst) = 0 →
      0 < s.mem (base + hdrNSrc) ∧ s.mem (base + hdrStage) = 0 ∧
      s.mem (base + hdrPhase) ≠ 1 ∧ s.mem (base + hdrPhase) ≠ 4 ∧ s.mem (base + hdrPhase) ≠ 5
  /-- Stage `1` only runs in phases `4..11` with `0 < nDst`. -/
  stg_one :
    s.mem (base + hdrStage) = 1 →
      0 < s.mem (base + hdrNDst) ∧ 4 ≤ s.mem (base + hdrPhase) ∧ s.mem (base + hdrPhase) ≤ 11
  /-- Trigger-time post-update hysteresis safety. -/
  post_trig : DualPostUpdateSafe c U (s.mem (base + hdrNSrc)) L.nTrig
  /-- Trigger decision witness producing `nDst`. -/
  trig_cap : dualTriggerCap c U (s.mem (base + hdrNSrc)) L.nTrig L.trigOps =
    some (s.mem (base + hdrNDst))
  /-- Upper drift of `nLive` from `L.nTrig`. -/
  drift_hi : nLive ≤ L.nTrig + (L.elapsed + (if isMid then 1 else 0))
  /-- Lower drift of `L.nTrig` from `nLive`. -/
  drift_lo : L.nTrig ≤ nLive + (L.elapsed + (if isMid then 1 else 0))
  /-- Low item-stream base formula across `ph < 10` vs `10 ≤ ph`. -/
  ibLo_eq :
    s.mem (base + hdrItemLo) =
      (if s.mem (base + hdrPhase) < 10 then base + 192 + s.mem (base + hdrMSrc)
       else base + 192 + s.mem (base + hdrMDst))
  /-- Low quotient width formula across `ph < 10` vs `10 ≤ ph`. -/
  qLo_eq :
    s.mem (base + hdrQLo) =
      (if s.mem (base + hdrPhase) < 10 then
         if s.mem (base + hdrNSrc) = 0 then keyBits U else quotBitsWhp U (s.mem (base + hdrNSrc))
       else
         if s.mem (base + hdrNDst) = 0 then keyBits U else quotBitsWhp U (s.mem (base + hdrNDst)))
  /-- Phase-1 (`log2Calc`) layout & frontier bounds. -/
  ph1 :
    s.mem (base + hdrPhase) = 1 →
      s.mem (base + hdrStage) = 0 ∧ 0 < s.mem (base + hdrNDst) ∧
      s.mem (base + hdrMDst) = 0 ∧
      s.mem (base + hdrItemHi) = s.mem (base + hdrItemLo) ∧
      s.mem (base + hdrQHi) = s.mem (base + hdrQLo) ∧
      s.mem (base + hdrItemLo) + pairStreamWords nLive (s.mem (base + hdrQLo)) (valBits V) w ≤
        s.frontier ∧
      s.frontier ≤
        s.mem (base + hdrItemLo) +
          pairStreamWords (nLive + (if isMid then 1 else 0)) (s.mem (base + hdrQLo)) (valBits V) w
  /-- Destination metadata, pad, host cache, and high stream layout for `2 ≤ ph`. -/
  ge2 :
    2 ≤ s.mem (base + hdrPhase) →
      s.mem (base + hdrMDst) = epochMetaWordsWhp c w (s.mem (base + hdrNDst)) ∧
      s.mem (base + hdrPad) = max (s.mem (base + hdrMSrc)) (s.mem (base + hdrMDst)) ∧
      HostCacheValid c w (s.mem (base + hdrNDst)) hdrDstOd base s.mem ∧
      (0 < s.mem (base + hdrNDst) →
        s.mem (base + hdrLogN) = Nat.log 2 (s.mem (base + hdrNDst)) ∧
        s.mem (base + hdrEll) = Dynamic.logLogFactor (s.mem (base + hdrNDst)) ∧
        s.mem (base + hdrPgB) = pageSizeWhp (s.mem (base + hdrNDst))) ∧
      s.mem (base + hdrItemHi) =
        (if s.mem (base + hdrNDst) = 0 then base + 196 + s.mem (base + hdrMSrc)
         else base + 192 + s.mem (base + hdrPad) + s.mem (base + hdrMDst) + 4) ∧
      s.mem (base + hdrQHi) =
        max (if s.mem (base + hdrNSrc) = 0 then keyBits U
             else quotBitsWhp U (s.mem (base + hdrNSrc)))
          (if s.mem (base + hdrNDst) = 0 then keyBits U
           else quotBitsWhp U (s.mem (base + hdrNDst)))
  /-- Phase-2 (`growPre`) frontier bounds. -/
  ph2 :
    s.mem (base + hdrPhase) = 2 →
      s.mem (base + hdrStage) = 0 ∧
      s.mem (base + hdrItemLo) + pairStreamWords nLive (s.mem (base + hdrQLo)) (valBits V) w ≤
        s.frontier ∧
      s.frontier ≤
        s.mem (base + hdrItemHi) +
          pairStreamWords (nLive + (if isMid then 1 else 0)) (s.mem (base + hdrQHi)) (valBits V) w
  /-- Phases `3..10` high-arena frontier bounds. -/
  ph3_10 :
    3 ≤ s.mem (base + hdrPhase) ∧ s.mem (base + hdrPhase) ≤ 10 →
      s.mem (base + hdrItemHi) + pairStreamWords nLive (s.mem (base + hdrQHi)) (valBits V) w ≤
        s.frontier ∧
      s.frontier ≤
        s.mem (base + hdrItemHi) +
          pairStreamWords (nLive + (if isMid then 1 else 0)) (s.mem (base + hdrQHi)) (valBits V) w
  /-- Phase-11 (`shrinkPost`) frontier bounds. -/
  ph11 :
    s.mem (base + hdrPhase) = 11 →
      s.mem (base + hdrItemLo) + pairStreamWords nLive (s.mem (base + hdrQLo)) (valBits V) w +
        (if isMid then 0 else 1) ≤ s.frontier ∧
      s.frontier ≤
        s.mem (base + hdrItemHi) +
          pairStreamWords (nLive + (if isMid then 1 else 0)) (s.mem (base + hdrQHi)) (valBits V) w
  /-- Countdown tick budget conservation (`16 * (elapsed + remB) ≤ nRef`). -/
  budget :
    let nRef := max (whpThreshold c) (s.mem (base + hdrNSrc))
    let pgH := dualPgHost c V w base nLive s.mem
    let ibHiTarget :=
      s.mem (base + hdrItemHi) + pairStreamWords nLive (s.mem (base + hdrQHi)) (valBits V) w
    let growDiff :=
      (ibHiTarget - s.frontier) + (if isMid ∧ s.frontier < ibHiTarget then 1022 else 0)
    let slideRem := (nLive - s.mem (base + hdrSplit)) - (if isMid then 1 else 0)
    let shrinkDiff :=
      (s.frontier -
        (s.mem (base + hdrItemLo) + pairStreamWords nLive (s.mem (base + hdrQLo)) (valBits V) w)) -
        (if isMid then 2 else 0)
    let offBM := if 0 < s.mem (base + hdrNDst) then offBktMeta c w (s.mem (base + hdrNDst)) else 0
    let remB := remRebuildBudget nRef (s.mem (base + hdrStage)) (s.mem (base + hdrPhase))
      (s.mem (base + hdrLogSub)) (s.mem (base + hdrLogK))
      growDiff (s.mem (base + hdrSplit)) slideRem
      (s.mem (base + hdrMDst)) offBM pgH.maxPages pgH.pgB
      (s.mem (base + hdrCur)) (s.mem (base + hdrRem)) shrinkDiff
    2 ≤ remB ∧
    16 * (L.elapsed + remB) ≤ nRef ∧
    16 * (L.elapsed + 2) ≤ nRef

/-- Shared structural invariant parameterized by `isMid : Bool` (`false` = resting `DualStateInv`,
`true` = mid-operation `DualMidInv` right before `bgTickProg`). -/
structure DualCoreInv (isMid : Bool) (c U V w base : ℕ) (s_dict : Dictionary.State U)
    (L : DualLatent c U V) (s : Memory.State) : Prop where
  /-- Word length lower bound `11 ≤ w`. -/
  hw11 : 11 ≤ w
  /-- Nonempty key universe `0 < U`. -/
  U_pos : 0 < U
  /-- Key universe fits strictly in one word `U < 2 ^ w`. -/
  U_lt : U < 2 ^ w
  /-- Nonempty value universe `0 < V`. -/
  V_pos : 0 < V
  /-- Value universe fits in `w` bits `V ≤ 2 ^ w`. -/
  V_le : V ≤ 2 ^ w
  /-- Ambient Word-RAM memory well-formedness. -/
  wf : Memory.WellFormed w s
  /-- Root header + both parameter tables fit below `s.frontier`. -/
  base_fr : base + 192 ≤ s.frontier
  /-- Static words `base + 0..9` match `(c, U, V, w)`. -/
  hdr : RootStaticHeader c U V w base s.mem
  /-- `hdrLive` equals `(Dictionary.dom s_dict).card`. -/
  live_eq : s.mem (base + hdrLive) = (Dictionary.dom s_dict).card
  /-- Live item count never exceeds `U`. -/
  live_le : (Dictionary.dom s_dict).card ≤ U
  /-- Phase index lies in `0..11`. -/
  ph_le : s.mem (base + hdrPhase) ≤ 11
  /-- Stage index lies in `0..1`. -/
  stg_le : s.mem (base + hdrStage) ≤ 1
  /-- `hdrMSrc` equals `epochMetaWordsWhp c w nSrc`. -/
  mSrc_eq : s.mem (base + hdrMSrc) = epochMetaWordsWhp c w (s.mem (base + hdrNSrc))
  /-- Source host-offset cache `38..42` is valid when `0 < nSrc`. -/
  cache_src : HostCacheValid c w (s.mem (base + hdrNSrc)) hdrSrcOd base s.mem
  /-- `nSrc` is `0` or in `[whpThreshold c, U]`. -/
  nSrc_bounds :
    s.mem (base + hdrNSrc) = 0 ∨
      (whpThreshold c ≤ s.mem (base + hdrNSrc) ∧ s.mem (base + hdrNSrc) ≤ U)
  /-- Idle (`ph = 0`) vs active (`1 ≤ ph ≤ 11`) schedule invariant. -/
  sched :
    if s.mem (base + hdrPhase) = 0 then
      DualIdleSched isMid c U V w base (Dictionary.dom s_dict).card L s
    else
      DualActiveSched isMid c U V w base (Dictionary.dom s_dict).card L s
  /-- `dualPaddedWords` ceiling fits strictly below `2 ^ w`. -/
  pad_fits :
    base + dualPaddedWords c U V w (s.mem (base + hdrNSrc))
      (if s.mem (base + hdrPhase) = 0 then s.mem (base + hdrNSrc) else s.mem (base + hdrNDst))
      (Dictionary.dom s_dict).card < 2 ^ w
  /-- Phase `1` (`log2Calc`) shift-register invariant. -/
  ph1_inv :
    s.mem (base + hdrPhase) = 1 →
      let nDst := s.mem (base + hdrNDst)
      let sub := s.mem (base + hdrLogSub)
      let acc := s.mem (base + hdrLogAcc)
      let lk := s.mem (base + hdrLogK)
      sub ≤ 2 ∧
      (sub = 0 → 1 ≤ acc ∧ acc * 2 ^ lk ≤ nDst ∧ nDst < (acc + 1) * 2 ^ lk) ∧
      (sub = 1 →
        s.mem (base + hdrLogN) = Nat.log 2 nDst ∧
        s.mem (base + hdrClogN) = Nat.clog 2 nDst ∧
        s.mem (base + hdrPtrB) = globalPtrBits nDst ∧
        s.mem (base + hdrPgB) = pageSizeWhp nDst ∧
        acc * 2 ^ lk ≤ Nat.clog 2 nDst - 1 ∧
        (1 ≤ acc → Nat.clog 2 nDst - 1 < (acc + 1) * 2 ^ lk) ∧
        (acc = 0 → lk = 0 ∧ Nat.clog 2 nDst ≤ 1)) ∧
      (sub = 2 →
        s.mem (base + hdrLogN) = Nat.log 2 nDst ∧
        s.mem (base + hdrEll) = Dynamic.logLogFactor nDst ∧
        s.mem (base + hdrPtrB) = globalPtrBits nDst ∧
        s.mem (base + hdrPgB) = pageSizeWhp nDst)
  /-- Phase `3` (`slideUp`) split-cursor & high-quotient invariant. -/
  ph3_inv :
    s.mem (base + hdrPhase) = 3 →
      s.mem (base + hdrSplit) ≤ (Dictionary.dom s_dict).card ∧
      SplitHiQuotBounded
        (splitSlotIo w (valBits V) base (s.mem (base + hdrItemLo)) (s.mem (base + hdrQLo))
          (s.mem (base + hdrItemHi)) (s.mem (base + hdrQHi)) (Dictionary.dom s_dict).card)
        (Dictionary.dom s_dict).card s.mem
  /-- Phase `4` (`zeroMeta`) prefix-zeroing invariant. -/
  ph4_inv :
    s.mem (base + hdrPhase) = 4 →
      0 < s.mem (base + hdrNDst) ∧ s.mem (base + hdrCur) ≤ s.mem (base + hdrMDst) ∧
      ∀ off < s.mem (base + hdrCur), s.mem (dualMbDst base s.mem + off) = 0
  /-- Pre-populated destination `ParamTable` (`0..47, 61, 62`) in phases `2..5` (`stg = 0` or
  `ph = 5`) when `0 < nDst`. -/
  pDst_pre :
    (2 ≤ s.mem (base + hdrPhase) ∧ s.mem (base + hdrPhase) ≤ 5) →
    (s.mem (base + hdrPhase) = 5 ∨ s.mem (base + hdrStage) = 0) →
    0 < s.mem (base + hdrNDst) →
      let nDst := s.mem (base + hdrNDst)
      let mbDst := dualMbDst base s.mem
      let pDst := dualPDst base s.mem
      let ibHi := s.mem (base + hdrItemHi)
      let qHi := s.mem (base + hdrQHi)
      let nLive := (Dictionary.dom s_dict).card
      ({ c := c, U := U, V := V, w := w, N := nDst, metaBase := mbDst, pBase := pDst,
         io := directSlotIo w (valBits V) base ibHi qHi nLive } : FastEpochLayout).ParamTable
        (dualPh5MaskMem V w base pDst ibHi qHi nLive s.mem)
  /-- Phase `5` (`randFill`) pre-populated `ParamTable` and zeroed metadata invariant. -/
  ph5_inv :
    s.mem (base + hdrPhase) = 5 →
      let nDst := s.mem (base + hdrNDst)
      let mbDst := dualMbDst base s.mem
      let pDst := dualPDst base s.mem
      let ibHi := s.mem (base + hdrItemHi)
      let qHi := s.mem (base + hdrQHi)
      let nLive := (Dictionary.dom s_dict).card
      0 < nDst ∧ 32 ≤ s.mem (base + hdrCur) ∧ s.mem (base + hdrCur) ≤ offBktMeta c w nDst ∧
      ({ c := c, U := U, V := V, w := w, N := nDst, metaBase := mbDst, pBase := pDst,
         io := directSlotIo w (valBits V) base ibHi qHi nLive } : FastEpochLayout).ParamTable
        (dualPh5MaskMem V w base pDst ibHi qHi nLive s.mem) ∧
      (∀ k, 1 ≤ k → k < 32 → s.mem (mbDst + k) = 0) ∧
      (∀ off, offBktMeta c w nDst ≤ off → off < offPageDir c w nDst → s.mem (mbDst + off) = 0)
  /-- Phase `6` (`initDir`) identity page-directory prefix invariant. -/
  ph6_inv :
    s.mem (base + hdrPhase) = 6 →
      let pgH := dualPgHost c V w base (Dictionary.dom s_dict).card s.mem
      s.mem (base + hdrCur) ≤ pgH.maxPages ∧
      (∀ vp < s.mem (base + hdrCur),
        (extractPagePair pgH s.mem).pageOf false vp = vp ∧
        (extractPagePair pgH s.mem).pageOf true vp = 0 ∧
        (extractPagePair pgH s.mem).ownerSide vp = false ∧
        (extractPagePair pgH s.mem).ownerVp vp = vp)
  /-- Phase `7` (`initTail`) directory + tail-ring prefix invariant. -/
  ph7_inv :
    s.mem (base + hdrPhase) = 7 →
      let nLive := (Dictionary.dom s_dict).card
      let pgH := dualPgHost c V w base nLive s.mem
      let nSnap := s.mem (base + hdrNSnap)
      let qSnap := s.mem (base + hdrQSnap)
      nSnap ≤ dualNHost base s.mem ∧
      qSnap = (if nSnap < pgH.pgB + (pgH.pgB + pgH.pgB / 2) then 0
        else (nSnap - (pgH.pgB + pgH.pgB / 2)) / pgH.pgB) ∧
      (∀ vp < pgH.maxPages,
        (extractPagePair pgH s.mem).pageOf false vp = vp ∧
        (extractPagePair pgH s.mem).pageOf true vp = 0 ∧
        (extractPagePair pgH s.mem).ownerSide vp = false ∧
        (extractPagePair pgH s.mem).ownerVp vp = vp) ∧
      (∃ k, s.mem (base + hdrCur) = 128 * k ∧ s.mem (base + hdrCur) < 8 * pgH.pgB ∧
        nSnap ≤ nLive + k + (if isMid then 1 else 0) ∧
        nLive ≤ nSnap + k + (if isMid then 1 else 0)) ∧
      (∀ idx < s.mem (base + hdrCur),
        (idx < 4 * pgH.pgB →
          (extractPagePair pgH s.mem).tailRes false idx =
            (qSnap * pgH.pgB + idx) % (8 * pgH.pgB) ∧
          (extractPagePair pgH s.mem).tailRes true idx =
            (qSnap * pgH.pgB + idx) % (8 * pgH.pgB)) ∧
        (extractPagePair pgH s.mem).tailOwnerSide idx = false ∧
        (extractPagePair pgH s.mem).tailOwnerRing idx =
          (idx + 8 * pgH.pgB - (qSnap * pgH.pgB) % (8 * pgH.pgB)) % (8 * pgH.pgB))
  /-- Phase `8` (`migrate`) remaining-item countdown invariant. -/
  ph8_inv :
    s.mem (base + hdrPhase) = 8 →
      1 ≤ s.mem (base + hdrRem) ∧
      s.mem (base + hdrRem) ≤ (2 * max (whpThreshold c) (s.mem (base + hdrNSrc))) / 1024 + 2 ∧
      (liveDom L.slotSrc.s_abs).card ≤ s.mem (base + hdrRem) * itemBatchWhp
  /-- Phase `9` (`unperm`) `unpermRank` countdown invariant. -/
  ph9_inv :
    s.mem (base + hdrPhase) = 9 →
      let pgH := dualPgHost c V w base (Dictionary.dom s_dict).card s.mem
      1 ≤ s.mem (base + hdrRem) ∧
      s.mem (base + hdrRem) ≤
        max (whpThreshold c) (s.mem (base + hdrNSrc)) / 240 + pgH.pgB / 8 + 4 ∧
      s.mem (base + hdrUnpermDone) ≤ 1 ∧
      (s.mem (base + hdrUnpermDone) = 0 →
        0 < (extractPageUnperm pgH s.mem).cleanPhase ∧
        (extractPageUnperm pgH s.mem).cleanPhase < 4 ∧
        (extractPageUnperm pgH s.mem).unpermRank ≤
          L.unpermBound + (if isMid then 64 else 0) ∧
        L.unpermBound ≤ s.mem (base + hdrRem) * (itemBatchWhp - 64))
  /-- Phase `10` (`slideDown`) split-cursor & high-quotient invariant. -/
  ph10_inv :
    s.mem (base + hdrPhase) = 10 →
      s.mem (base + hdrSplit) ≤ (Dictionary.dom s_dict).card ∧
      SplitHiQuotBounded
        (splitSlotIo w (valBits V) base (s.mem (base + hdrItemLo)) (s.mem (base + hdrQLo))
          (s.mem (base + hdrItemHi)) (s.mem (base + hdrQHi)) (Dictionary.dom s_dict).card)
        (Dictionary.dom s_dict).card s.mem
  /-- Source-slot `EpochSlotInv` coupling in phases `0..7`. -/
  sl_le7 :
    s.mem (base + hdrPhase) ≤ 7 →
      L.slotSrc.nCap = dualCapSrc base s.mem ∧
      toDictState L.slotSrc.s_abs = s_dict ∧
      EpochSlotInv c U V w s.frontier (dualPSrc base s.mem) (dualMbSrc base s.mem)
        (activeSrcIo c w (valBits V) base (s.mem (base + hdrStage)) (s.mem (base + hdrPhase))
          (s.mem (base + hdrNSrc)) (s.mem (base + hdrNDst)) (s.mem (base + hdrPad))
          (s.mem (base + hdrItemLo)) (s.mem (base + hdrQLo)) (s.mem (base + hdrItemHi))
          (s.mem (base + hdrQHi)) (Dictionary.dom s_dict).card)
        0 false L.slotSrc s.mem ∧
      (0 < s.mem (base + hdrPhase) → 0 < dualCapSrc base s.mem →
        L.slotSrc.evs.length ≤ 2 * dualCapSrc base s.mem + L.elapsed + (if isMid then 1 else 0))
  /-- Initialized empty destination-slot `EpochSlotInv` (or zeroed `hdrSmallMeta1`) in phases
  `6, 7`. -/
  sl_67 :
    (s.mem (base + hdrPhase) = 6 ∨ s.mem (base + hdrPhase) = 7) →
      (s.mem (base + hdrNDst) = 0 →
        s.mem (base + hdrSmallMeta1) = 0 ∧ s.mem (base + hdrSmallMeta1 + 1) = 0) ∧
      (0 < s.mem (base + hdrNDst) →
        L.slotDst.nCap = s.mem (base + hdrNDst) ∧
        L.slotDst.s_abs = (fun _ => none) ∧
        L.slotDst.evs = [] ∧
        EpochSlotInv c U V w s.frontier (dualPDst base s.mem) (dualMbDst base s.mem)
          (directSlotIo w (valBits V) base (s.mem (base + hdrItemHi)) (s.mem (base + hdrQHi))
            (Dictionary.dom s_dict).card)
          0 false L.slotDst s.mem)
  /-- Dual paged `EpochSlotInv` coupling in Phase `8` (`migrate`). -/
  sl_8 :
    s.mem (base + hdrPhase) = 8 →
      let pgH := dualPgHost c V w base (Dictionary.dom s_dict).card s.mem
      L.slotSrc.nCap = dualCapSrc base s.mem ∧ L.slotDst.nCap = s.mem (base + hdrNDst) ∧
      DisjointOpt L.slotDst.s_abs L.slotSrc.s_abs ∧
      toDictState (orOpt L.slotDst.s_abs L.slotSrc.s_abs) = s_dict ∧
      (extractPageUnperm pgH s.mem).cleanPhase = 0 ∧
      EpochSlotInv c U V w s.frontier (dualPSrc base s.mem) (dualMbSrc base s.mem)
        (pagedSlotIo 0 pgH) 0 true L.slotSrc s.mem ∧
      EpochSlotInv c U V w s.frontier (dualPDst base s.mem) (dualMbDst base s.mem)
        (pagedSlotIo 1 pgH) 0 false L.slotDst s.mem ∧
      (0 < dualCapSrc base s.mem → L.slotSrc.evs.length ≤ 3 * dualCapSrc base s.mem) ∧
      (0 < s.mem (base + hdrNDst) →
        L.slotDst.evs.length + (liveDom L.slotSrc.s_abs).card ≤
          s.mem (base + hdrNDst) + L.elapsed + (if isMid then 1 else 0))
  /-- Destination-slot `EpochSlotInv` coupling in phases `9..11`. -/
  sl_ge9 :
    9 ≤ s.mem (base + hdrPhase) →
      L.slotDst.nCap = s.mem (base + hdrNDst) ∧
      toDictState L.slotDst.s_abs = s_dict ∧
      EpochSlotInv c U V w s.frontier (dualPDst base s.mem) (dualMbDst base s.mem)
        (activeDstIo c w (valBits V) base (s.mem (base + hdrStage)) (s.mem (base + hdrPhase))
          (s.mem (base + hdrNSrc)) (s.mem (base + hdrNDst)) (s.mem (base + hdrPad))
          (s.mem (base + hdrItemLo)) (s.mem (base + hdrQLo)) (s.mem (base + hdrItemHi))
          (s.mem (base + hdrQHi)) (Dictionary.dom s_dict).card (s.mem (base + hdrUnpermDone)))
        (if isMid ∧ s.mem (base + hdrPhase) = 9 ∧ s.mem (base + hdrUnpermDone) = 0 then 24 else 0)
        false L.slotDst s.mem ∧
      (0 < s.mem (base + hdrNDst) →
        L.slotDst.evs.length ≤ s.mem (base + hdrNDst) + L.elapsed + (if isMid then 1 else 0))

/-- Resting 12-phase dual-epoch memory and frontier invariant between dictionary operations. -/
@[expose] def DualStateInv (c U V w base : ℕ) (s_dict : Dictionary.State U)
    (L : DualLatent c U V) (s : Memory.State) : Prop :=
  DualCoreInv false c U V w base s_dict L s

/-- Mid-operation dual-epoch invariant immediately after `userMutateProg` and before `bgTickProg`.
-/
@[expose] def DualMidInv (c U V w base : ℕ) (s_dict : Dictionary.State U)
    (L : DualLatent c U V) (s : Memory.State) : Prop :=
  DualCoreInv true c U V w base s_dict L s

/-- Combined fast-path seed coverage of active epoch slots at phase `ph`. -/
@[expose] def DualLatent.ActiveGood {c U V : ℕ} (ph : ℕ) (L : DualLatent c U V) : Prop :=
  (ph ≤ 8 → L.slotSrc.GoodCovers) ∧ (8 ≤ ph → L.slotDst.GoodCovers)

/-- Initial empty `DualLatent` at `ph = 0, nSrc = 0, nDst = 0`. -/
@[expose] noncomputable def DualLatent.empty (c U V : ℕ) : DualLatent c U V where
  slotSrc := SlotLatent.emptySmall c U V
  slotDst := SlotLatent.emptySmall c U V
  nTrig := 0
  trigOps := 0
  elapsed := 0
  unpermBound := 0

/-- `initDualRootProg` on a freshly zeroed `194`-word arena establishes `DualStateInv` for
`Dictionary.empty U`. -/
theorem dualStateInv_init {c U V w base : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s)
    (hw11 : 11 ≤ w) (hU0 : 0 < U) (hUw : U < 2 ^ w) (hV0 : 0 < V) (hVw : V ≤ 2 ^ w)
    (hfr : s.frontier = base + 194)
    (hzero : ∀ off < 194, s.mem (base + off) = 0)
    (hpad_fits : base + dualPaddedWords c U V w 0 0 0 < 2 ^ w) :
    let s' := (Memory.spec 0).clientState s (initDualRootProg c U V w base)
    s'.frontier = base + 194 ∧
    memoryCost (initDualRootProg c U V w base) s ≤ 60 ∧
    (∀ addr, addr < base → s'.mem addr = s.mem addr) ∧
    DualStateInv c U V w base (Dictionary.empty U) (DualLatent.empty c U V) s' := by
  dsimp only
  obtain ⟨_, _, _, hkb_le, _, hvb_le, _, _, _, _, _, _, _⟩ :=
    static_hdr_fits (c := c) hw11 hU0 hUw hV0 hVw
  set io0 := directSlotIo w (valBits V) base (base + 192) (keyBits U) 0
  let L0 : SmallEpochLayout := ⟨base + hdrSmallMeta0, U, V, io0⟩
  let L1 : SmallEpochLayout := ⟨base + hdrSmallMeta1, U, V, io0⟩
  set s1 := (Memory.spec 0).clientState s (initRootStaticAProg c U V w base)
  set s2 := (Memory.spec 0).clientState s1 (initRootStaticBProg c U base)
  set s3 := (Memory.spec 0).clientState s2
    (writeSmallConstProg hdrPBase0 hdrSmallMeta0 w (initValBitsVal V) (initKeyBitsVal U) base)
  set s4 := (Memory.spec 0).clientState s3
    (writeSmallConstProg hdrPBase1 hdrSmallMeta1 w (initValBitsVal V) (initKeyBitsVal U) base)
  have hst_eq : (Memory.spec 0).clientState s (initDualRootProg c U V w base) = s4 := by
    unfold initDualRootProg
    repeat rw [cstate_seqUnit]
  have hs3_sp := writeSmallConst_spec U V hdrPBase0 hdrSmallMeta0 w
    (initValBitsVal V) (initKeyBitsVal U) base s2
  have hs4_sp := writeSmallConst_spec U V hdrPBase1 hdrSmallMeta1 w
    (initValBitsVal V) (initKeyBitsVal U) base s3
  have hs1_out : ∀ a, ¬(base ≤ a ∧ a < base + 7) → s1.mem a = s.mem a := fun a ha => by
    unfold s1 initRootStaticAProg hdrU1 hdrV1 hdrW hdrKeyBits hdrValBits hdrThresh hdrCTab
    repeat rw [cstate_seqUnit]
    repeat rw [cstate_writeConstAt]
    dsimp only
    iterate 7 rw [Function.update_of_ne (by omega)]
  have hs2_out : ∀ a, ¬(base + 7 ≤ a ∧ a < base + 10 ∨ base + 22 ≤ a ∧ a < base + 26) →
      s2.mem a = s1.mem a := fun a ha => by
    unfold s2 initRootStaticBProg hdrDTab hdrRedW hdrCEff hdrItemLo hdrItemHi hdrQLo hdrQHi
    repeat rw [cstate_seqUnit]
    repeat (first | rw [cstate_writeConstAt] | rw [cstate_writeAddConstAt])
    dsimp only
    iterate 7 rw [Function.update_of_ne (by omega)]
  have hlow_eq : ∀ off < 64, s4.mem (base + off) = s2.mem (base + off) := fun off hoff =>
    (hs4_sp.2.2.2 (base + off) (by unfold hdrPBase1; omega)).trans
      (hs3_sp.2.2.2 (base + off) (by unfold hdrPBase0; omega))
  have hfr4 : s4.frontier = base + 194 := by
    rw [hs4_sp.1, hs3_sp.1, initRootStaticB_fr, initRootStaticA_fr, hfr]
  have hmc : memoryCost (initDualRootProg c U V w base) s ≤ 60 := by
    unfold initDualRootProg
    repeat rw [mcost_seqUnit]
    have hmc_a : memoryCost (initRootStaticAProg c U V w base) s = 7 := initRootStaticA_mc ..
    have hmc_b : memoryCost (initRootStaticBProg c U base) s1 = 7 := initRootStaticB_mc ..
    have hmc0 := hs3_sp.2.1
    have hmc1 := hs4_sp.2.1
    dsimp only [s1, s2, s3] at hmc_b hmc0 hmc1
    rw [hmc_a, hmc_b, hmc0, hmc1]
    omega
  have hwf4 : Memory.WellFormed w s4 := by
    rw [← hst_eq]
    exact wf_step hwf (validHistory_initDualRootProg hwf hw11 hU0 hUw hV0 hVw (by omega))
  have hhdr : RootStaticHeader c U V w base s4.mem := by
    have h0_6 : ∀ k < 7, s2.mem (base + k) = s1.mem (base + k) := fun k hk =>
      hs2_out (base + k) (by omega)
    have hs1_v : s1.mem (base + 0) = U - 1 ∧ s1.mem (base + 1) = V - 1 ∧
        s1.mem (base + 2) = w ∧ s1.mem (base + 3) = keyBits U ∧
        s1.mem (base + 4) = valBits V ∧
        s1.mem (base + 5) = (if whpThreshold c ≤ U then whpThreshold c else 0) ∧
        s1.mem (base + 6) = (if whpThreshold c ≤ U then cTabWhp c else 0) := by
      rw [← initU1Val_eq, ← initV1Val_eq, ← initKeyBitsVal_eq, ← initValBitsVal_eq,
        ← initThreshVal_eq, ← initCTabVal_eq]
      unfold s1 initRootStaticAProg hdrU1 hdrV1 hdrW hdrKeyBits hdrValBits hdrThresh hdrCTab
      repeat rw [cstate_seqUnit]
      repeat rw [cstate_writeConstAt]
      dsimp only
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, Function.update_self ..⟩
      · iterate 6 rw [Function.update_of_ne (by omega)]
        exact Function.update_self ..
      · iterate 5 rw [Function.update_of_ne (by omega)]
        exact Function.update_self ..
      · iterate 4 rw [Function.update_of_ne (by omega)]
        exact Function.update_self ..
      · iterate 3 rw [Function.update_of_ne (by omega)]
        exact Function.update_self ..
      · iterate 2 rw [Function.update_of_ne (by omega)]
        exact Function.update_self ..
      · rw [Function.update_of_ne (by omega)]
        exact Function.update_self ..
    have hs2_v : s2.mem (base + 7) = (if whpThreshold c ≤ U then dTabWhp c else 0) ∧
        s2.mem (base + 8) = redWidthWhp U ∧
        s2.mem (base + 9) = (if whpThreshold c ≤ U then cEff c else 0) ∧
        s2.mem (base + 22) = base + 192 ∧ s2.mem (base + 23) = base + 192 ∧
        s2.mem (base + 24) = keyBits U ∧ s2.mem (base + 25) = keyBits U := by
      rw [← initDTabVal_eq, ← initRedWVal_eq, ← initCEffVal_eq, ← initKeyBitsVal_eq]
      unfold s2 initRootStaticBProg hdrDTab hdrRedW hdrCEff hdrItemLo hdrItemHi hdrQLo hdrQHi
      repeat rw [cstate_seqUnit]
      repeat (first | rw [cstate_writeConstAt] | rw [cstate_writeAddConstAt])
      dsimp only
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, Function.update_self ..⟩
      · iterate 6 rw [Function.update_of_ne (by omega)]
        exact Function.update_self ..
      · iterate 5 rw [Function.update_of_ne (by omega)]
        exact Function.update_self ..
      · iterate 4 rw [Function.update_of_ne (by omega)]
        exact Function.update_self ..
      · iterate 3 rw [Function.update_of_ne (by omega)]
        exact Function.update_self ..
      · iterate 2 rw [Function.update_of_ne (by omega)]
        exact Function.update_self ..
      · rw [Function.update_of_ne (by omega)]
        exact Function.update_self ..
    exact ⟨(hlow_eq 0 (by decide)).trans ((h0_6 0 (by decide)).trans hs1_v.1),
      (hlow_eq 1 (by decide)).trans ((h0_6 1 (by decide)).trans hs1_v.2.1),
      (hlow_eq 2 (by decide)).trans ((h0_6 2 (by decide)).trans hs1_v.2.2.1),
      (hlow_eq 3 (by decide)).trans ((h0_6 3 (by decide)).trans hs1_v.2.2.2.1),
      (hlow_eq 4 (by decide)).trans ((h0_6 4 (by decide)).trans hs1_v.2.2.2.2.1),
      (hlow_eq 5 (by decide)).trans ((h0_6 5 (by decide)).trans hs1_v.2.2.2.2.2.1),
      (hlow_eq 6 (by decide)).trans ((h0_6 6 (by decide)).trans hs1_v.2.2.2.2.2.2),
      (hlow_eq 7 (by decide)).trans hs2_v.1,
      (hlow_eq 8 (by decide)).trans hs2_v.2.1,
      (hlow_eq 9 (by decide)).trans hs2_v.2.2.1⟩
  have hz_mid : ∀ off, (10 ≤ off ∧ off < 22 ∨ 26 ≤ off ∧ off < 64) → s4.mem (base + off) = 0 :=
    fun off hoff => by
      rw [hlow_eq off (by omega), hs2_out (base + off) (by omega),
        hs1_out (base + off) (by omega)]
      exact hzero off (by omega)
  have hib_vals : s4.mem (base + hdrItemLo) = base + 192 ∧
      s4.mem (base + hdrItemHi) = base + 192 ∧
      s4.mem (base + hdrQLo) = keyBits U ∧
      s4.mem (base + hdrQHi) = keyBits U := by
    rw [← initKeyBitsVal_eq]
    unfold hdrItemLo hdrItemHi hdrQLo hdrQHi
    rw [hlow_eq 22 (by decide), hlow_eq 23 (by decide), hlow_eq 24 (by decide),
      hlow_eq 25 (by decide)]
    unfold s2 initRootStaticBProg hdrDTab hdrRedW hdrCEff hdrItemLo hdrItemHi hdrQLo hdrQHi
    repeat rw [cstate_seqUnit]
    repeat (first | rw [cstate_writeConstAt] | rw [cstate_writeAddConstAt])
    dsimp only
    refine ⟨?_, ?_, ?_, Function.update_self ..⟩
    · iterate 3 rw [Function.update_of_ne (by omega)]
      exact Function.update_self ..
    · iterate 2 rw [Function.update_of_ne (by omega)]
      exact Function.update_self ..
    · rw [Function.update_of_ne (by omega)]
      exact Function.update_self ..
  have hpw0 : pairStreamWords 0 (keyBits U) (valBits V) w = 2 := by
    unfold pairStreamWords packedWords
    simp [Nat.div_eq_of_lt (show w - 1 < w by omega)]
  have hm0_eq : epochMetaWordsWhp c w 0 = 0 := by
    unfold epochMetaWordsWhp; rw [ite_eq_left (whpThreshold_pos c)]
  have hdom_empty : (Dictionary.dom (Dictionary.empty U)).card = 0 := by simp
  rw [hst_eq]
  refine ⟨hfr4, hmc, fun addr ha => ?_, ?_⟩
  · rw [hs4_sp.2.2.2 addr (by unfold hdrPBase1; omega),
      hs3_sp.2.2.2 addr (by unfold hdrPBase0; omega),
      hs2_out addr (by omega), hs1_out addr (by omega)]
  · unfold DualStateInv
    have hnL : s4.mem (base + hdrLive) = 0 := hz_mid 10 (Or.inl ⟨by decide, by decide⟩)
    have hph : s4.mem (base + hdrPhase) = 0 := hz_mid 11 (Or.inl ⟨by decide, by decide⟩)
    have hstg : s4.mem (base + hdrStage) = 0 := hz_mid 12 (Or.inl ⟨by decide, by decide⟩)
    have hnS : s4.mem (base + hdrNSrc) = 0 := hz_mid 13 (Or.inl ⟨by decide, by decide⟩)
    have hnD : s4.mem (base + hdrNDst) = 0 := hz_mid 14 (Or.inl ⟨by decide, by decide⟩)
    have hmS : s4.mem (base + hdrMSrc) = 0 := hz_mid 19 (Or.inl ⟨by decide, by decide⟩)
    have hmD : s4.mem (base + hdrMDst) = 0 := hz_mid 20 (Or.inl ⟨by decide, by decide⟩)
    have hsm0_0 : s4.mem (base + hdrSmallMeta0) = 0 := hz_mid 48 (Or.inr ⟨by decide, by decide⟩)
    have hsm0_1 : s4.mem (base + hdrSmallMeta0 + 1) = 0 :=
      hz_mid 49 (Or.inr ⟨by decide, by decide⟩)
    have hpt0 : L0.ParamTable (base + hdrPBase0) s4.mem := by
      have hp0' : SmallEpochLayout.ParamTable
          ⟨base + hdrSmallMeta0, U, V,
            directSlotIo w (initValBitsVal V) base (base + 192) (initKeyBitsVal U) 0⟩
          (base + hdrPBase0) s4.mem :=
        hs3_sp.2.2.1.congr fun a h1 h2 =>
          hs4_sp.2.2.2 a (by unfold hdrPBase0 hdrPBase1 at *; omega)
      have hconv : ∀ (m : ℕ → ℕ),
          SmallEpochLayout.ParamTable
            ⟨base + hdrSmallMeta0, U, V,
              directSlotIo w (initValBitsVal V) base (base + 192) (initKeyBitsVal U) 0⟩
            (base + hdrPBase0) m →
          L0.ParamTable (base + hdrPBase0) m := by
        intro m hm
        rwa [initValBitsVal_eq, initKeyBitsVal_eq] at hm
      exact hconv s4.mem hp0'
    have hv_L0 : L0.Valid w s4.frontier :=
      { io_valid := by
          unfold SlotIoLayout.Valid
          dsimp only [L0, io0, directSlotIo, ↓reduceIte]
          rw [hfr4, hpw0]
          exact ⟨by omega, rfl, hkb_le, hvb_le, Nat.two_pow_pos w, le_rfl⟩
        w_eq := rfl
        qBits_eq := rfl
        vBits_eq := rfl
        hdr_frontier := by dsimp only [L0]; rw [hfr4]; unfold hdrSmallMeta0; omega
        disjoint_hdr := fun addr hmb hia => by
          simp only [L0, io0, directSlotIo, SlotIoLayout.OwnsAddr, PageArenaLayout.OwnsItemAddr,
            hdrSmallMeta0, ↓reduceIte] at hmb hia
          rcases hmb with rfl | rfl <;> omega }
    have hsl0 : EpochSlotInv c U V w s4.frontier (base + hdrPBase0) (base + hdrSmallMeta0)
        io0 0 false (SlotLatent.emptySmall c U V) s4.mem := by
      unfold EpochSlotInv; dsimp only [SlotLatent.emptySmall, ↓reduceIte]
      refine ⟨by omega, by rw [hfr4]; unfold hdrPBase0; omega, hv_L0, hpt0,
        fun a h1 h2 ha => ?_, hsm0_0, by simp only [io0, directSlotIo]; omega,
        by
          unfold SlotIoLayout.StateInv
          simp only [io0, directSlotIo, ↓reduceIte, hsm0_1, le_rfl, true_and]
          exact Or.inl trivial,
        ⟨fun p hp => by rw [hsm0_1] at hp; omega,
         fun p hp => by rw [hsm0_1] at hp; omega,
         fun u v => ⟨fun h => (by cases h),
           fun ⟨p, hp, _⟩ => by rw [hsm0_1] at hp; omega⟩⟩⟩
      simp only [SmallEpochLayout.OwnsAddr, SlotIoLayout.OwnsAddr, PageArenaLayout.OwnsItemAddr,
        io0, directSlotIo, hdrPBase0, hdrSmallMeta0, ↓reduceIte] at h1 h2 ha
      omega
    refine
      { hw11 := hw11
        U_pos := hU0
        U_lt := hUw
        V_pos := hV0
        V_le := hVw
        wf := hwf4
        base_fr := by omega
        hdr := hhdr
        live_eq := hnL.trans hdom_empty.symm
        live_le := hdom_empty ▸ Nat.zero_le U
        ph_le := by rw [hph]; decide
        stg_le := by rw [hstg]; decide
        mSrc_eq := by rw [hmS, hnS]; exact hm0_eq.symm
        cache_src := fun h => by rw [hnS] at h; exact absurd h (Nat.lt_irrefl 0)
        nSrc_bounds := Or.inl hnS
        sched := by
          rw [ite_eq_left hph]
          refine
            { stg_zero := hstg
              nDst_zero := hnD
              mDst_zero := hmD
              ibLo_eq := by rw [hib_vals.1, hmS]
              ibHi_eq := hib_vals.2.1.trans hib_vals.1.symm
              qLo_eq := by rw [hib_vals.2.2.1, hnS, ite_eq_left rfl]
              qHi_eq := hib_vals.2.2.2.trans hib_vals.2.2.1.symm
              elapsed_zero := rfl
              safe_fr := by
                rw [ite_eq_right Bool.false_ne_true, hdom_empty, hnS, hib_vals.1, hib_vals.2.2.1]
                exact ⟨dualIdleSafe_empty c U, fun _ => whpThreshold_pos c, by rw [hfr4, hpw0]⟩
              ops_evs := fun h => by rw [hnS] at h; exact absurd h (Nat.lt_irrefl 0) }
        pad_fits := by rw [hnS, ite_eq_left hph, hdom_empty]; exact hpad_fits
        ph1_inv := fun h => by rw [hph] at h; cases h
        ph3_inv := fun h => by rw [hph] at h; cases h
        ph4_inv := fun h => by rw [hph] at h; cases h
        pDst_pre := fun h _ _ => by rw [hph] at h; omega
        ph5_inv := fun h => by rw [hph] at h; cases h
        ph6_inv := fun h => by rw [hph] at h; cases h
        ph7_inv := fun h => by rw [hph] at h; cases h
        ph8_inv := fun h => by rw [hph] at h; cases h
        ph9_inv := fun h => by rw [hph] at h; cases h
        ph10_inv := fun h => by rw [hph] at h; cases h
        sl_le7 := fun _ => by
          unfold dualCapSrc dualPSrc dualMbSrc
          rw [hstg, hnS, hph, hib_vals.1, hib_vals.2.1, hib_vals.2.2.1, hib_vals.2.2.2, hdom_empty]
          refine ⟨rfl, rfl, ?_, fun h => absurd h (Nat.lt_irrefl 0)⟩
          simpa [activeSrcIo, DualLatent.empty, io0] using hsl0
        sl_67 := fun h => by rw [hph] at h; rcases h with h | h <;> cases h
        sl_8 := fun h => by rw [hph] at h; cases h
        sl_ge9 := fun h => by rw [hph] at h; omega }

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

end
