/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpSwarProg

/-!
# Fast-Mode Transition Frame Invariant (`FastStateStep`) and Large-Regime Bounds

This module defines the compositional transition invariant `FastStateStep` for fast-mode
`Memory.Prog` subroutines on `FastMemRep`, together with:

1. Large-regime index and capacity bounds (`large_index_bounds`, `bufTrie_caps_of_bounds`).
2. `FastStateStep` reflexivity/transitivity, `bTreeSliceMemRep_congr`, and `FastMemRep`
   slice/buffer projections (`FastMemRep.slice_rep`, `FastMemRep.buf_rep`).
3. `CostBoundedStep`, the final state, result, cost bound and validity of one run of a
   `Memory.Prog`, with its `pure`/`bind`/`if` composition rules.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.FastStateStep`: compositional invariant
  preserving `SeedWhpMemRep`, `FastMemRep`, `frontier`, and memory outside `largeSpaceWhp`.
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.CostBoundedStep`: running a program from
  a given state ends in a given state with a given result, within a cost bound, and validly.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.large_index_bounds`,
  `bTreeSliceMemRep_congr`, `bufTrie_caps_of_bounds`.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.WordRAM
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct

/-! ## Section 1: Segment and Index Bounds -/

/-- Auxiliary index bounds in the large regime (`whpThreshold c ≤ n_max`). -/
theorem large_index_bounds {c n_max : ℕ} (hth : whpThreshold c ≤ n_max) :
    numBucketsWhp n_max * capBackWhp n_max ≤ n_max ∧
    numBucketsWhp n_max * capFrontWhp n_max + poolSizeWhp n_max = n_max ∧
    2 * totalLocalCoordsWhp n_max + 32 ≤ n_max ∧
    poolSizeWhp n_max ≤ n_max ∧
    3 * numBucketsWhp n_max ≤ n_max ∧
    6 * qEpochWhp n_max + 6 ≤ n_max := by
  have hL2 := two_le_slabScale n_max
  have hML12 := numBucketsWhp_mul_scale_pow12_le hth
  have h16M := sixteen_mul_numBuckets_le_n_max hth
  obtain ⟨hM_ge, _, _, _, _, _, _, _⟩ := large_bounds_lt_n_max hth
  obtain ⟨_, _, _, _, _, hq6_le⟩ := sublinear_table_bits_le hth
  have hg_pos := globalPtrBits_pos_of_large hth
  have h6q : 6 * qEpochWhp n_max + 6 ≤ n_max :=
    (Nat.le_mul_of_pos_right _ hg_pos).trans hq6_le
  have hcb_le : capBackWhp n_max ≤ (slabScale n_max) ^ 12 := by
    unfold capBackWhp
    rw [show (slabScale n_max) ^ 12 = slabScale n_max * (slabScale n_max) ^ 11 by ring]
    exact Nat.mul_le_mul_right _ hL2
  have hmcb : numBucketsWhp n_max * capBackWhp n_max ≤ n_max :=
    (Nat.mul_le_mul_left _ hcb_le).trans hML12
  have hmcf : numBucketsWhp n_max * capFrontWhp n_max ≤ n_max :=
    (Nat.mul_le_mul_left _ (Nat.sub_le _ _)).trans (Nat.mul_div_le _ _)
  have hps_eq : numBucketsWhp n_max * capFrontWhp n_max + poolSizeWhp n_max = n_max := by
    unfold poolSizeWhp; omega
  have h2tl : 2 * totalLocalCoordsWhp n_max + 32 ≤ n_max := by
    have := totalLocalCoordsWhp_le_three_mul (n_max := n_max)
    have := (Nat.mul_le_mul_right _ hM_ge).trans hML12
    have := Nat.one_le_pow 12 (slabScale n_max) (by omega)
    omega
  exact ⟨hmcb, hps_eq, h2tl, by omega, by omega, h6q⟩

/-! ## Section 2: `FastStateStep` and `FastMemRep` Projections -/

/-- Bundled transition invariant for fast-mode `Memory.Prog` substeps: preserves `frontier`,
`SeedWhpMemRep`, `FastMemRep` for `fs'`, and all memory words outside
`[base, base + largeSpaceWhp c U V w n_max)`. -/
@[expose] def FastStateStep (base c U V w n_max : ℕ) (θ : SeedWhp c U n_max)
    (fs' : FastState) (s s' : Memory.State) : Prop :=
  s'.frontier = s.frontier ∧
  SeedWhpMemRep base c U w n_max θ s'.mem ∧
  FastMemRep base c U V w n_max fs' s'.mem ∧
  (∀ a, (a < base ∨ base + largeSpaceWhp c U V w n_max ≤ a) → s'.mem a = s.mem a)

theorem FastStateStep.refl {base c U V w n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {s : Memory.State}
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    FastStateStep base c U V w n_max θ fs s s :=
  ⟨rfl, hseed, hrep, fun _ _ => rfl⟩

theorem FastStateStep.trans {base c U V w n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs₁ fs₂ : FastState} {s₀ s₁ s₂ : Memory.State}
    (h₁ : FastStateStep base c U V w n_max θ fs₁ s₀ s₁)
    (h₂ : FastStateStep base c U V w n_max θ fs₂ s₁ s₂) :
    FastStateStep base c U V w n_max θ fs₂ s₀ s₂ :=
  ⟨h₂.1.trans h₁.1, h₂.2.1, h₂.2.2.1, fun a ha => (h₂.2.2.2 a ha).trans (h₁.2.2.2 a ha)⟩

/-- `BTreeSliceMemRep` invariance when `offBktMeta` (`[10..15]`) and `[offBtMeta, offTrieChild0)`
are unchanged. -/
theorem bTreeSliceMemRep_congr {base c U V w n_max sIdx : ℕ} {sl : BTreeSlice}
    {mem₁ mem₂ : ℕ → ℕ} (hw : 0 < w) (hsIdx : sIdx < 3 * numBucketsWhp n_max)
    (hbm : readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w mem₂
        (16 * (sIdx / 3) + 10 + 2 * (sIdx % 3)) =
      readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w mem₁
        (16 * (sIdx / 3) + 10 + 2 * (sIdx % 3)) ∧
      readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w mem₂
        (16 * (sIdx / 3) + 11 + 2 * (sIdx % 3)) =
      readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w mem₁
        (16 * (sIdx / 3) + 11 + 2 * (sIdx % 3)))
    (hbt : ∀ a, base + offBtMeta c U V w n_max ≤ a → a < base + offTrieChild0 c U V w n_max →
      mem₂ a = mem₁ a)
    (hrep : BTreeSliceMemRep base c U V w n_max sIdx sl mem₁) :
    BTreeSliceMemRep base c U V w n_max sIdx sl mem₂ := by
  have hch := largeOffsetChain c U V w n_max
  obtain ⟨ha_le, ha_r, hr_r, hnd⟩ := hrep
  refine ⟨ha_le, hbm.1.trans ha_r, hbm.2.trans hr_r, fun u hu => ?_⟩
  have hidx : sIdx * nSliceWhp n_max + u < totalBTreeNodesWhp n_max := by
    unfold totalBTreeNodesWhp
    exact mul_add_lt_mul_bound hsIdx (hu.trans_le ha_le)
  exact ⟨(readPacked_congr hw (hidx := hidx) fun a ⟨h1,
    h2⟩ => hbt a h1 (by omega)).trans (hnd u hu).1,
    (readPacked_congr hw (hidx := hidx) fun a ⟨h1,
      h2⟩ => hbt a (by omega) (by omega)).trans (hnd u hu).2.1,
    (readPacked_congr hw (hidx := hidx) fun a ⟨h1,
      h2⟩ => hbt a (by omega) (by omega)).trans (hnd u hu).2.2⟩

theorem FastMemRep.slice_rep {base c U V w n_max sIdx : ℕ} {fs : FastState} {mem : ℕ → ℕ}
    (hsIdx : sIdx < 3 * numBucketsWhp n_max)
    (hrep : FastMemRep base c U V w n_max fs mem) :
    BTreeSliceMemRep base c U V w n_max sIdx (fs.slices sIdx) mem :=
  hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 sIdx hsIdx

theorem FastMemRep.buf_rep {base c U V w n_max ep : ℕ} {fs : FastState} {mem : ℕ → ℕ}
    (hep : ep = 0 ∨ ep = 1)
    (hrep : FastMemRep base c U V w n_max fs mem) :
    BufTrieMemRep base c U V w n_max ep (fs.buf ep) mem := by
  rcases hep with rfl | rfl
  · exact hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem bufTrie_caps_of_bounds {c n_max : ℕ} (hth : whpThreshold c ≤ n_max) {tr : BufTrie}
    (hia : tr.itemAlloc ≤ 2 * sMaxWhp c n_max)
    (hna : tr.nodeAlloc ≤ 1 + cTabWhp c * tr.itemAlloc) :
    tr.nodeAlloc + cTabWhp c ≤ maxTrieNodesWhp c n_max ∧
    tr.itemAlloc < qEpochWhp n_max := by
  have hlt := two_mul_rIndepWhp_lt_qEpochWhp hth
  have hia_lt : tr.itemAlloc < qEpochWhp n_max := hia.trans_lt hlt
  refine ⟨?_, hia_lt⟩
  unfold maxTrieNodesWhp
  calc tr.nodeAlloc + cTabWhp c
      ≤ 1 + cTabWhp c * tr.itemAlloc + cTabWhp c := Nat.add_le_add_right hna _
    _ = 1 + cTabWhp c * (tr.itemAlloc + 1) := by ring
    _ ≤ 1 + cTabWhp c * qEpochWhp n_max := Nat.add_le_add_left (Nat.mul_le_mul_left _ hia_lt) 1
    _ ≤ (cTabWhp c + 1) * qEpochWhp n_max + 2 := by nlinarith

/-! ## Section 3: Cost-Bounded Steps -/

/-- `CostBoundedStep w F s p s' r C`: running the memory program `p` from state `s` ends in state
`s'` with result `r`, issues at most `C` memory operations (`memoryCost`), and produces a valid
memory history at word size `w` whenever `s` is well formed with frontier at least `F`
(`ValidProg`). -/
structure CostBoundedStep {α : Type} (w F : ℕ) (s : Memory.State) (p : Memory.Prog α)
    (s' : Memory.State) (r : α) (C : ℕ) : Prop where
  /-- Final memory state produced by `p` from `s`. -/
  clientState_eq : (Memory.spec 0).clientState s p = s'
  /-- Result returned by `p` from `s`. -/
  clientResult_eq : (Memory.spec 0).clientResult s p = r
  /-- Upper bound on memory operations issued by `p` from `s`. -/
  memoryCost_le : memoryCost p s ≤ C
  /-- Memory-history validity of `p` from `s` at word size `w` and frontier `F`. -/
  validProg : ValidProg w F s p

namespace CostBoundedStep

variable {α : Type} {w F C C' : ℕ} {s s' : Memory.State}

/-- A run that leaves the state unchanged at exact cost `C` is a cost-bounded step. -/
theorem of {p : Memory.Prog α} {r : α}
    (h : (Memory.spec 0).clientState s p = s ∧ (Memory.spec 0).clientResult s p = r ∧
      memoryCost p s = C ∧ ValidProg w F s p) : CostBoundedStep w F s p s r C :=
  let ⟨h1, h2, h3, h4⟩ := h
  ⟨h1, h2, h3.le, h4⟩

/-- Pure return takes zero memory operations and leaves the state unchanged. -/
theorem pure (s : Memory.State) (x : α) : CostBoundedStep w F s (Pure.pure x) s x 0 :=
  ⟨rfl, rfl, (memoryCost_pure x s).le, validProg_pure x⟩

/-- Sequential composition sums cost bounds and threads the intermediate state and result. -/
theorem bind {β : Type} {C₁ C₂ : ℕ} {s₁ s₂ : Memory.State} {f : Memory.Prog α}
    {g : α → Memory.Prog β} {x : α} {y : β} (hf : CostBoundedStep w F s f s₁ x C₁)
    (hg : CostBoundedStep w F s₁ (g x) s₂ y C₂) :
    CostBoundedStep w F s (f >>= g) s₂ y (C₁ + C₂) where
  clientState_eq := by
    rw [StateTransitionSpec.clientState_bind, hf.clientState_eq, hf.clientResult_eq,
      hg.clientState_eq]
  clientResult_eq := by
    rw [StateTransitionSpec.clientResult_bind, hf.clientState_eq, hf.clientResult_eq,
      hg.clientResult_eq]
  memoryCost_le := by
    rw [memoryCost_bind', hf.clientState_eq, hf.clientResult_eq]
    exact Nat.add_le_add hf.memoryCost_le hg.memoryCost_le
  validProg := validProg_bind hf.validProg (by
    rw [hf.clientState_eq, hf.clientResult_eq]
    exact hg.validProg)

/-- Relax the memory-operation upper bound of a cost-bounded step. -/
theorem mono {p : Memory.Prog α} {r : α} (h : CostBoundedStep w F s p s' r C) (hC : C ≤ C') :
    CostBoundedStep w F s p s' r C' :=
  ⟨h.clientState_eq, h.clientResult_eq, h.memoryCost_le.trans hC, h.validProg⟩

/-- Conditional execution with matching final state and cost bound across both branches. -/
theorem ite {c : Prop} [Decidable c] {p₁ p₂ : Memory.Prog α} {r₁ r₂ : α}
    (h₁ : CostBoundedStep w F s p₁ s' r₁ C) (h₂ : CostBoundedStep w F s p₂ s' r₂ C) :
    CostBoundedStep w F s (if c then p₁ else p₂) s' (if c then r₁ else r₂) C := by
  split_ifs <;> assumption

/-- Positive branch of a conditional cost-bounded step. -/
theorem if_pos {c : Prop} [Decidable c] {p₁ p₂ : Memory.Prog α} {r : α} (hc : c)
    (h : CostBoundedStep w F s p₁ s' r C) :
    CostBoundedStep w F s (if c then p₁ else p₂) s' r C := by
  rwa [ite_eq_left hc]

/-- Negative branch of a conditional cost-bounded step. -/
theorem if_neg {c : Prop} [Decidable c] {p₁ p₂ : Memory.Prog α} {r : α} (hc : ¬c)
    (h : CostBoundedStep w F s p₂ s' r C) :
    CostBoundedStep w F s (if c then p₁ else p₂) s' r C := by
  rwa [ite_eq_right hc]

/-- Read a cost-bounded step off as a cost bound, validity and a property of the final state. -/
theorem elim {p : Memory.Prog α} {r : α} {P : Memory.State → Prop}
    (h : CostBoundedStep w F s p s' r C) (hC : C ≤ C') (hP : P s') :
    memoryCost p s ≤ C' ∧ ValidProg w F s p ∧ P ((Memory.spec 0).clientState s p) :=
  ⟨h.memoryCost_le.trans hC, h.validProg, by rw [h.clientState_eq]; exact hP⟩

end CostBoundedStep

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
