/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeMetaProg
import CslibFrontier.Computability.WordRAM.Realization.BoundedTactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Bit-Packed `BufTrie` `Memory.Prog` Primitives and Exact Refinement

This module couples the pure bounded-depth character trie buffer `BufTrie`
(`Cslib.DataStructure.Dictionary.SuccinctWhp`) to bit-packed Word-RAM memory inside a large epoch's
metadata region (`offTrieChild`, `offTrieNode`, `offTrieItem`), proves `RealizesBounded .exact`
(`¬ReadsWidth`) for every trie operation (`bufLookupBoundedProg`, `bufInsertBoundedProg`,
`bufDeleteBoundedProg`, `bufCheckSlotBoundedProg`, `bufClearStepsBoundedProg`), and establishes
exact functional refinement (`extractBufTrie ... = bufInsert ...`, `bufDelete`, `bufClearSteps`)
together with memory frame preservation outside the modified trie copy's slices.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.TrieLayout`, `epochTrieLayout`,
  `extractBufTrie`: named memory layout and pure `BufTrie` extractor.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.bufLookupBoundedProg`,
  `bufInsertBoundedProg`, `bufDeleteBoundedProg`, `bufCheckSlotBoundedProg`,
  `bufClearStepsBoundedProg`: overflow-free `Memory.Prog` primitives.

## Main results

* `realizesBounded_bufLookup`, `realizesBounded_bufInsert`, `realizesBounded_bufDelete`,
  `realizesBounded_bufCheckSlot`, `realizesBounded_bufClearSteps`: `RealizesBounded .exact`
  certificates (`¬ReadsWidth`).
* `bufLookupBoundedProg_spec`, `bufInsertBoundedProg_spec`, `bufDeleteBoundedProg_spec`,
  `bufCheckSlotBoundedProg_spec`, `bufClearStepsBoundedProg_spec`: exact `extractBufTrie`
  refinement and frame preservation theorems.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, and W. Kuszmaul, *Modern Hashing Made Simple*,
  Section 5][BenderFarachColtonKuszmaulKuszmaul2024]
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

attribute [local simp] Realization.memoryCost_bind'
attribute [local simp] prog_clientResult_bind prog_runClient_state_bind prog_clientResult_pure
attribute [local simp] prog_runClient_state_pure prog_clientResult_map prog_runClient_state_map
attribute [local simp] prog_memoryCost_map prog_clientResult_read prog_runClient_state_read
attribute [local simp] prog_memoryCost_read prog_clientResult_write prog_runClient_state_write
attribute [local simp] prog_memoryCost_write

/-! ## Section 1: `TrieLayout`, `extractBufTrie`, and Disjointness Frame Lemmas -/

/-- Named memory layout descriptor for one bit-packed `BufTrie` copy (`0` projection chains). -/
structure TrieLayout where
  /-- Base word address of the enclosing epoch metadata region. -/
  metaBase : ℕ
  /-- Word offset of the `(maxNodes * 2 ^ bChar)`-entry child pointer array. -/
  offChild : ℕ
  /-- Word offset of the `(6 * maxNodes)`-entry node metadata array. -/
  offNode : ℕ
  /-- Word offset of the `(6 * qMax + 6)`-entry item-log and `(nodeAlloc, itemAlloc)` array. -/
  offItem : ℕ
  /-- Bit-width `globalPtrBits N` of each packed entry. -/
  ptrB : ℕ
  /-- Machine word bit-width `w`. -/
  w : ℕ
  /-- Number of character levels `cTabWhp c`. -/
  cTab : ℕ
  /-- Character bit-width `bCharWhp N`. -/
  bChar : ℕ
  /-- Node capacity `maxTrieNodesWhp c N`. -/
  maxNodes : ℕ
  /-- Item-log capacity `qEpochWhp N`. -/
  qMax : ℕ

/-- Concrete `TrieLayout` for buffer copy `role ∈ {0, 1}` of a large epoch `(c, w, N)` at
`metaBase`. -/
@[expose] def epochTrieLayout (c w N metaBase role : ℕ) : TrieLayout where
  metaBase := metaBase
  offChild := offTrieChild c w N role
  offNode := offTrieNode c w N role
  offItem := offTrieItem c w N role
  ptrB := globalPtrBits N
  w := w
  cTab := cTabWhp c
  bChar := bCharWhp N
  maxNodes := maxTrieNodesWhp c N
  qMax := qEpochWhp N

/-- Tuple encoding of `TrieLayout` for `RealizesBounded` `Memory.Prog` primitives. -/
abbrev TrieCtx := ((ℕ × ℕ) × (ℕ × ℕ)) × ((ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ)))

/-- Pack a `TrieLayout` into `TrieCtx`. -/
@[expose] def TrieLayout.toCtx (L : TrieLayout) : TrieCtx :=
  (((L.metaBase, L.offChild), (L.offNode, L.offItem)),
    ((L.ptrB, L.w), ((L.cTab, L.bChar), (L.maxNodes, L.qMax))))

/-- Unpack a `TrieCtx` into `TrieLayout`. -/
@[expose] def TrieLayout.ofCtx : TrieCtx → TrieLayout
  | (((mb, oc), (on_, oi)), ((pb, wv), ((ct, bc), (mn, qm)))) =>
    ⟨mb, oc, on_, oi, pb, wv, ct, bc, mn, qm⟩

@[simp] theorem TrieLayout.ofCtx_toCtx (L : TrieLayout) :
    TrieLayout.ofCtx L.toCtx = L := by
  cases L; rfl

/-- Word-interval predicate for the three bit-packed arrays owned by `L`. -/
@[expose] def TrieLayout.OwnsAddr (L : TrieLayout) (addr : ℕ) : Prop :=
  (L.metaBase + L.offChild ≤ addr ∧
    addr < L.metaBase + L.offChild + packedWords (L.maxNodes * 2 ^ L.bChar) L.ptrB L.w) ∨
  (L.metaBase + L.offNode ≤ addr ∧
    addr < L.metaBase + L.offNode + packedWords (6 * L.maxNodes) L.ptrB L.w) ∨
  (L.metaBase + L.offItem ≤ addr ∧
    addr < L.metaBase + L.offItem + packedWords (6 * L.qMax + 6) L.ptrB L.w)

/-- Static parameter and frontier-safety invariant for `TrieLayout`. -/
@[expose] def TrieLayout.Valid (L : TrieLayout) (w_mach frontier : ℕ) : Prop :=
  0 < w_mach ∧ w_mach = L.w ∧ L.ptrB ≤ w_mach ∧ 0 < L.bChar ∧ L.bChar < w_mach ∧
  2 ^ L.bChar ≤ 2 ^ L.ptrB ∧ 1 ≤ L.maxNodes ∧ L.maxNodes < 2 ^ L.ptrB ∧ L.qMax < 2 ^ L.ptrB ∧
  L.cTab < 2 ^ w_mach ∧
  L.maxNodes * 2 ^ L.bChar < 2 ^ w_mach ∧
  6 * L.maxNodes < 2 ^ w_mach ∧
  6 * L.qMax + 6 < 2 ^ w_mach ∧
  L.offChild + packedWords (L.maxNodes * 2 ^ L.bChar) L.ptrB L.w ≤ L.offNode ∧
  L.offNode + packedWords (6 * L.maxNodes) L.ptrB L.w ≤ L.offItem ∧
  L.metaBase + L.offItem + packedWords (6 * L.qMax + 6) L.ptrB L.w ≤ frontier

/-- `epochTrieLayout` satisfies `TrieLayout.Valid` for both `role = 0` and `role = 1` whenever
`whpThreshold c ≤ N ≤ U < 2 ^ w` and `metaBase + epochMetaWordsWhp c w N ≤ frontier`. -/
theorem valid_epochTrieLayout {c U w N metaBase role frontier : ℕ}
    (hth : whpThreshold c ≤ N) (hNU : N ≤ U) (hU : Fits w U) (hrole : role < 2)
    (hfr : metaBase + epochMetaWordsWhp c w N ≤ frontier) :
    (epochTrieLayout c w N metaBase role).Valid w frontier := by
  obtain ⟨hptr_lt, hptr_w, hlog_w, hbc_w, _, _, _, _, _, _, _, _, htc_le, htm_le, htl_le,
    _, _, _, _, _⟩ := largeEpoch_param_bounds hth hNU hU
  have hw_pos : 0 < w := by omega
  have hU_lt : N < 2 ^ w := lt_of_le_of_lt hNU hU
  have hbc_pos : 0 < bCharWhp N := by
    have h1 := Dynamic.one_le_logLogFactor N
    have h2 := (Nat.mul_le_mul_right _ (le_codeExpWhp c)).trans (codeExpWhp_mul_ell_le_bCharWhp hth)
    have h3 := le_codeExpWhp c
    nlinarith
  have hpow_bc_N : 2 ^ bCharWhp N ≤ N := by
    have hmn_pos : 1 ≤ maxTrieNodesWhp c N := by unfold maxTrieNodesWhp; omega
    calc 2 ^ bCharWhp N ≤ maxTrieNodesWhp c N * 2 ^ bCharWhp N :=
          Nat.le_mul_of_pos_left _ hmn_pos
      _ ≤ N := htc_le
  have hmn_le : maxTrieNodesWhp c N ≤ N := by omega
  have hq_le : qEpochWhp N ≤ N := by omega
  have hct_le : cTabWhp c ≤ maxTrieNodesWhp c N := by
    unfold maxTrieNodesWhp qEpochWhp
    have hq1 : 1 ≤ slabScale N ^ 18 := Nat.one_le_pow 18 _ (by have := two_le_slabScale N; omega)
    nlinarith
  have hend := offEpochEnd_eq_epochMetaWordsWhp (c := c) (w := w) hth
  refine ⟨hw_pos, rfl, hptr_w, hbc_pos, hbc_w, hpow_bc_N.trans hptr_lt.le,
    by dsimp only [epochTrieLayout]; unfold maxTrieNodesWhp; omega,
    lt_of_le_of_lt hmn_le hptr_lt,
    lt_of_le_of_lt hq_le hptr_lt, lt_of_le_of_lt (hct_le.trans hmn_le) hU_lt,
    lt_of_le_of_lt htc_le hU_lt, lt_of_le_of_lt htm_le hU_lt, lt_of_le_of_lt htl_le hU_lt,
    ?_, ?_, ?_⟩
  · rcases role with _ | _ | _ <;> try omega
    all_goals (dsimp only [epochTrieLayout, offTrieNode, offTrieChild, trieChildWords]; omega)
  · rcases role with _ | _ | _ <;> try omega
    all_goals (dsimp only [epochTrieLayout, offTrieItem, offTrieNode, trieNodeWords]; omega)
  · rcases role with _ | _ | _ <;> try omega
    all_goals (
      dsimp only [epochTrieLayout]
      unfold offEpochEnd at hend
      unfold offPageTail offPageDir at hend
      unfold offTrieItem trieItemWords at hend ⊢
      omega)

/-- Distinct buffer roles `role₀ ≠ role₁` (`< 2`) own completely disjoint word sets. -/
theorem epochTrieLayout_disjoint {c w N metaBase role₀ role₁ addr : ℕ}
    (hr₀ : role₀ < 2) (hr₁ : role₁ < 2) (hne : role₀ ≠ role₁)
    (h₀ : (epochTrieLayout c w N metaBase role₀).OwnsAddr addr) :
    ¬(epochTrieLayout c w N metaBase role₁).OwnsAddr addr := by
  intro h₁
  dsimp only [epochTrieLayout, TrieLayout.OwnsAddr, offTrieChild, offTrieNode, offTrieItem,
    trieChildWords, trieNodeWords, trieItemWords] at h₀ h₁
  rcases role₀ with _ | _ | _ <;> try omega
  all_goals (rcases role₁ with _ | _ | _ <;> omega)

/-- Pure extraction of a `BufTrie` from bit-packed memory according to `L`. -/
@[expose] def extractBufTrie (L : TrieLayout) (mem : ℕ → ℕ) : BufTrie where
  nodeAlloc := readPacked (L.metaBase + L.offItem) L.ptrB L.w mem (6 * L.qMax)
  itemAlloc := readPacked (L.metaBase + L.offItem) L.ptrB L.w mem (6 * L.qMax + 1)
  trieChild := fun v ch =>
    if v < L.maxNodes ∧ ch < 2 ^ L.bChar then
      readPacked (L.metaBase + L.offChild) L.ptrB L.w mem ((v <<< L.bChar) + ch)
    else 0
  nodeParent := fun u =>
    if u < L.maxNodes then readPacked (L.metaBase + L.offNode) L.ptrB L.w mem (6 * u) else 0
  nodeChar := fun u =>
    if u < L.maxNodes then readPacked (L.metaBase + L.offNode) L.ptrB L.w mem (6 * u + 1) else 0
  nodeLeafItem := fun u =>
    if u < L.maxNodes then readPacked (L.metaBase + L.offNode) L.ptrB L.w mem (6 * u + 2) else 0
  nodeActive := fun u =>
    if u < L.maxNodes then readPacked (L.metaBase + L.offNode) L.ptrB L.w mem (6 * u + 3) else 0
  itemLeaf := fun id =>
    if id < L.qMax then readPacked (L.metaBase + L.offItem) L.ptrB L.w mem (6 * id) else 0
  itemBucket := fun id =>
    if id < L.qMax then readPacked (L.metaBase + L.offItem) L.ptrB L.w mem (6 * id + 1) else 0
  itemLoc := fun id =>
    if id < L.qMax then readPacked (L.metaBase + L.offItem) L.ptrB L.w mem (6 * id + 2) else 0

/-- Frame theorem: `extractBufTrie L` depends only on addresses satisfying `L.OwnsAddr`. -/
theorem extractBufTrie_congr {L : TrieLayout} {mem₁ mem₂ : ℕ → ℕ} (hw : 0 < L.w)
    (heq : ∀ addr, L.OwnsAddr addr → mem₁ addr = mem₂ addr) :
    extractBufTrie L mem₁ = extractBufTrie L mem₂ := by
  have hc : ∀ idx < L.maxNodes * 2 ^ L.bChar,
      readPacked (L.metaBase + L.offChild) L.ptrB L.w mem₁ idx =
        readPacked (L.metaBase + L.offChild) L.ptrB L.w mem₂ idx := fun idx hidx =>
    readPacked_congr hw (fun addr ha => heq addr (Or.inl ha)) hidx
  have hn : ∀ idx < 6 * L.maxNodes,
      readPacked (L.metaBase + L.offNode) L.ptrB L.w mem₁ idx =
        readPacked (L.metaBase + L.offNode) L.ptrB L.w mem₂ idx := fun idx hidx =>
    readPacked_congr hw (fun addr ha => heq addr (Or.inr (Or.inl ha))) hidx
  have hi : ∀ idx < 6 * L.qMax + 6,
      readPacked (L.metaBase + L.offItem) L.ptrB L.w mem₁ idx =
        readPacked (L.metaBase + L.offItem) L.ptrB L.w mem₂ idx := fun idx hidx =>
    readPacked_congr hw (fun addr ha => heq addr (Or.inr (Or.inr ha))) hidx
  unfold extractBufTrie
  congr 1
  · exact hi (6 * L.qMax) (by omega)
  · exact hi (6 * L.qMax + 1) (by omega)
  · ext v ch
    split_ifs with hv
    · refine hc ((v <<< L.bChar) + ch) ?_
      rw [Nat.shiftLeft_eq]
      calc v * 2 ^ L.bChar + ch < v * 2 ^ L.bChar + 2 ^ L.bChar := Nat.add_lt_add_left hv.2 _
        _ = (v + 1) * 2 ^ L.bChar := by ring
        _ ≤ L.maxNodes * 2 ^ L.bChar := Nat.mul_le_mul_right _ hv.1
    · rfl
  · ext u; split_ifs with hu
    · exact hn (6 * u) (by omega)
    · rfl
  · ext u; split_ifs with hu
    · exact hn (6 * u + 1) (by omega)
    · rfl
  · ext u; split_ifs with hu
    · exact hn (6 * u + 2) (by omega)
    · rfl
  · ext u; split_ifs with hu
    · exact hn (6 * u + 3) (by omega)
    · rfl
  · ext id; split_ifs with hid
    · exact hi (6 * id) (by omega)
    · rfl
  · ext id; split_ifs with hid
    · exact hi (6 * id + 1) (by omega)
    · rfl
  · ext id; split_ifs with hid
    · exact hi (6 * id + 2) (by omega)
    · rfl

/-- When all words in `L.OwnsAddr` are zero and we write `nodeAlloc := 1` at `6 * L.qMax`,
`extractBufTrie` equals `emptyBufTrie` identically. -/
theorem extractBufTrie_init_empty {L : TrieLayout} {mem : ℕ → ℕ}
    (hw : 0 < L.w) (hptr1 : 1 < 2 ^ L.ptrB)
    (hdisj1 : L.offChild + packedWords (L.maxNodes * 2 ^ L.bChar) L.ptrB L.w ≤ L.offNode)
    (hdisj2 : L.offNode + packedWords (6 * L.maxNodes) L.ptrB L.w ≤ L.offItem)
    (hzero : ∀ addr, L.OwnsAddr addr → mem addr = 0) :
    let mem' := writePacked (L.metaBase + L.offItem) L.ptrB L.w mem (6 * L.qMax) 1
    extractBufTrie L mem' = emptyBufTrie := by
  intro mem'
  have hidx_na : 6 * L.qMax < 6 * L.qMax + 6 := by omega
  have hout_I : ∀ addr, ¬(L.metaBase + L.offItem ≤ addr ∧
      addr < L.metaBase + L.offItem + packedWords (6 * L.qMax + 6) L.ptrB L.w) →
      mem' addr = mem addr := fun addr ha =>
    writePacked_outside hw mem hidx_na 1 ha
  have hzC : ∀ idx < L.maxNodes * 2 ^ L.bChar,
      readPacked (L.metaBase + L.offChild) L.ptrB L.w mem' idx = 0 := fun idx hidx => by
    have hlt := wordOffset_add_one_lt_packedWords (k := L.ptrB) hw hidx
    refine readPacked_zero ?_ ?_
    · rw [hout_I _ (by omega)]; exact hzero _ (Or.inl ⟨by omega, by omega⟩)
    · rw [hout_I _ (by omega)]; exact hzero _ (Or.inl ⟨by omega, by omega⟩)
  have hzN : ∀ idx < 6 * L.maxNodes,
      readPacked (L.metaBase + L.offNode) L.ptrB L.w mem' idx = 0 := fun idx hidx => by
    have hlt := wordOffset_add_one_lt_packedWords (k := L.ptrB) hw hidx
    refine readPacked_zero ?_ ?_
    · rw [hout_I _ (by omega)]; exact hzero _ (Or.inr (Or.inl ⟨by omega, by omega⟩))
    · rw [hout_I _ (by omega)]; exact hzero _ (Or.inr (Or.inl ⟨by omega, by omega⟩))
  have hzI : ∀ idx < 6 * L.qMax + 6, idx ≠ 6 * L.qMax →
      readPacked (L.metaBase + L.offItem) L.ptrB L.w mem' idx = 0 := fun idx hidx hne => by
    rw [readPacked_writePacked_of_ne hw mem hne 1]
    have hlt := wordOffset_add_one_lt_packedWords (k := L.ptrB) hw hidx
    exact readPacked_zero
      (hzero _ (Or.inr (Or.inr ⟨by omega, by omega⟩)))
      (hzero _ (Or.inr (Or.inr ⟨by omega, by omega⟩)))
  unfold extractBufTrie emptyBufTrie
  congr 1
  · exact readPacked_writePacked_self _ _ _ mem (6 * L.qMax) hptr1
  · exact hzI (6 * L.qMax + 1) (by omega) (by omega)
  · ext v ch
    split_ifs with hv
    · refine hzC ((v <<< L.bChar) + ch) ?_
      rw [Nat.shiftLeft_eq]
      calc v * 2 ^ L.bChar + ch < v * 2 ^ L.bChar + 2 ^ L.bChar := Nat.add_lt_add_left hv.2 _
        _ = (v + 1) * 2 ^ L.bChar := by ring
        _ ≤ L.maxNodes * 2 ^ L.bChar := Nat.mul_le_mul_right _ hv.1
    · rfl
  · ext u; split_ifs with hu
    · exact hzN (6 * u) (by omega)
    · rfl
  · ext u; split_ifs with hu
    · exact hzN (6 * u + 1) (by omega)
    · rfl
  · ext u; split_ifs with hu
    · exact hzN (6 * u + 2) (by omega)
    · rfl
  · ext u; split_ifs with hu
    · exact hzN (6 * u + 3) (by omega)
    · rfl
  · ext id; split_ifs with hid
    · exact hzI (6 * id) (by omega) (by omega)
    · rfl
  · ext id; split_ifs with hid
    · exact hzI (6 * id + 1) (by omega) (by omega)
    · rfl
  · ext id; split_ifs with hid
    · exact hzI (6 * id + 2) (by omega) (by omega)
    · rfl

/-! ## Section 2: Exact Update Lemmas on `extractBufTrie` -/

private theorem child_idx_lt {bChar maxNodes v ch : ℕ} (hv : v < maxNodes) (hch : ch < 2 ^ bChar) :
    (v <<< bChar) + ch < maxNodes * 2 ^ bChar := by
  rw [Nat.shiftLeft_eq]
  calc v * 2 ^ bChar + ch < v * 2 ^ bChar + 2 ^ bChar := Nat.add_lt_add_left hch _
    _ = (v + 1) * 2 ^ bChar := by ring
    _ ≤ maxNodes * 2 ^ bChar := Nat.mul_le_mul_right _ hv

private theorem extractBufTrie_writeChild {L : TrieLayout} {mem : ℕ → ℕ} {v ch val : ℕ}
    (hvL : L.Valid L.w (L.metaBase + L.offItem + packedWords (6 * L.qMax + 6) L.ptrB L.w))
    (hv : v < L.maxNodes) (hch : ch < 2 ^ L.bChar) (hval : val < 2 ^ L.ptrB) :
    let tr := extractBufTrie L mem
    let mem' := writePacked (L.metaBase + L.offChild) L.ptrB L.w mem ((v <<< L.bChar) + ch) val
    extractBufTrie L mem' =
      { tr with
        trieChild := Function.update tr.trieChild v (Function.update (tr.trieChild v) ch val) }
      ∧ ∀ addr, ¬L.OwnsAddr addr → mem' addr = mem addr := by
  intro tr mem'
  obtain ⟨hw, _, _, _, _, _, _, _, _, _, _, _, _, hd1, hd2, _⟩ := hvL
  have hidx := child_idx_lt hv hch
  have houtC : ∀ addr, ¬(L.metaBase + L.offChild ≤ addr ∧
      addr < L.metaBase + L.offChild + packedWords (L.maxNodes * 2 ^ L.bChar) L.ptrB L.w) →
      mem' addr = mem addr := fun addr ha => writePacked_outside hw mem hidx val ha
  have hn_eq : ∀ idx < 6 * L.maxNodes,
      readPacked (L.metaBase + L.offNode) L.ptrB L.w mem' idx =
        readPacked (L.metaBase + L.offNode) L.ptrB L.w mem idx := fun idx hi =>
    readPacked_congr hw (fun addr ha => houtC addr (by omega)) hi
  have hi_eq : ∀ idx < 6 * L.qMax + 6,
      readPacked (L.metaBase + L.offItem) L.ptrB L.w mem' idx =
        readPacked (L.metaBase + L.offItem) L.ptrB L.w mem idx := fun idx hi =>
    readPacked_congr hw (fun addr ha => houtC addr (by omega)) hi
  refine ⟨?_, fun addr ha => houtC addr fun hc => ha (Or.inl hc)⟩
  dsimp only [tr, extractBufTrie]
  congr 1
  · exact hi_eq (6 * L.qMax) (by omega)
  · exact hi_eq (6 * L.qMax + 1) (by omega)
  · ext v' ch'
    by_cases heq : v' = v ∧ ch' = ch
    · obtain ⟨rfl, rfl⟩ := heq
      simp only [hv, hch, and_self, ↓reduceIte, Function.update_self]
      exact readPacked_writePacked_self _ _ _ mem _ hval
    · have hupd : Function.update
          (fun v0 ch0 => if v0 < L.maxNodes ∧ ch0 < 2 ^ L.bChar then
            readPacked (L.metaBase + L.offChild) L.ptrB L.w mem ((v0 <<< L.bChar) + ch0) else 0)
          v (Function.update
            (fun ch0 => if v < L.maxNodes ∧ ch0 < 2 ^ L.bChar then
              readPacked (L.metaBase + L.offChild) L.ptrB L.w mem ((v <<< L.bChar) + ch0) else 0)
            ch val) v' ch' =
          if v' < L.maxNodes ∧ ch' < 2 ^ L.bChar then
            readPacked (L.metaBase + L.offChild) L.ptrB L.w mem ((v' <<< L.bChar) + ch')
          else 0 := by
        by_cases hv_eq : v' = v
        · subst hv_eq
          have hch_ne : ch' ≠ ch := fun hc => heq ⟨rfl, hc⟩
          simp [Function.update_self, Function.update_of_ne hch_ne]
        · simp [Function.update_of_ne hv_eq]
      rw [hupd]
      split_ifs with hv'
      · refine readPacked_writePacked_of_ne hw mem (fun hidx_eq => heq ?_) val
        rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq] at hidx_eq
        have hv_div : (v' * 2 ^ L.bChar + ch') / 2 ^ L.bChar = v' := by
          rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
            Nat.div_eq_of_lt hv'.2, zero_add]
        have hv_div2 : (v * 2 ^ L.bChar + ch) / 2 ^ L.bChar = v := by
          rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
            Nat.div_eq_of_lt hch, zero_add]
        have hve : v' = v := by rw [← hv_div, hidx_eq, hv_div2]
        exact ⟨hve, by subst hve; omega⟩
      · rfl
  · ext u; split_ifs with hu
    · exact hn_eq (6 * u) (by omega)
    · rfl
  · ext u; split_ifs with hu
    · exact hn_eq (6 * u + 1) (by omega)
    · rfl
  · ext u; split_ifs with hu
    · exact hn_eq (6 * u + 2) (by omega)
    · rfl
  · ext u; split_ifs with hu
    · exact hn_eq (6 * u + 3) (by omega)
    · rfl
  · ext id; split_ifs with hid
    · exact hi_eq (6 * id) (by omega)
    · rfl
  · ext id; split_ifs with hid
    · exact hi_eq (6 * id + 1) (by omega)
    · rfl
  · ext id; split_ifs with hid
    · exact hi_eq (6 * id + 2) (by omega)
    · rfl

private theorem extractBufTrie_writeNodeField {L : TrieLayout} {mem : ℕ → ℕ} {u fld val : ℕ}
    (hvL : L.Valid L.w (L.metaBase + L.offItem + packedWords (6 * L.qMax + 6) L.ptrB L.w))
    (hu : u < L.maxNodes) (hfld : fld < 4) (hval : val < 2 ^ L.ptrB) :
    let tr := extractBufTrie L mem
    let mem' := writePacked (L.metaBase + L.offNode) L.ptrB L.w mem (6 * u + fld) val
    extractBufTrie L mem' =
      (match fld with
       | 0 => { tr with nodeParent := Function.update tr.nodeParent u val }
       | 1 => { tr with nodeChar := Function.update tr.nodeChar u val }
       | 2 => { tr with nodeLeafItem := Function.update tr.nodeLeafItem u val }
       | _ => { tr with nodeActive := Function.update tr.nodeActive u val }) ∧
      ∀ addr, ¬L.OwnsAddr addr → mem' addr = mem addr := by
  intro tr mem'
  obtain ⟨hw, _, _, _, _, _, _, _, _, _, _, _, _, hd1, hd2, _⟩ := hvL
  have hidx : 6 * u + fld < 6 * L.maxNodes := by omega
  have houtN : ∀ addr, ¬(L.metaBase + L.offNode ≤ addr ∧
      addr < L.metaBase + L.offNode + packedWords (6 * L.maxNodes) L.ptrB L.w) →
      mem' addr = mem addr := fun addr ha => writePacked_outside hw mem hidx val ha
  have hc_eq : ∀ idx < L.maxNodes * 2 ^ L.bChar,
      readPacked (L.metaBase + L.offChild) L.ptrB L.w mem' idx =
        readPacked (L.metaBase + L.offChild) L.ptrB L.w mem idx := fun idx hi =>
    readPacked_congr hw (fun addr ha => houtN addr (by omega)) hi
  have hi_eq : ∀ idx < 6 * L.qMax + 6,
      readPacked (L.metaBase + L.offItem) L.ptrB L.w mem' idx =
        readPacked (L.metaBase + L.offItem) L.ptrB L.w mem idx := fun idx hi =>
    readPacked_congr hw (fun addr ha => houtN addr (by omega)) hi
  have hupd_f : ∀ f < 4,
      (fun u' => if u' < L.maxNodes then
        readPacked (L.metaBase + L.offNode) L.ptrB L.w mem' (6 * u' + f) else 0) =
      if f = fld then
        Function.update (fun u' => if u' < L.maxNodes then
          readPacked (L.metaBase + L.offNode) L.ptrB L.w mem (6 * u' + f) else 0) u val
      else
        (fun u' => if u' < L.maxNodes then
          readPacked (L.metaBase + L.offNode) L.ptrB L.w mem (6 * u' + f) else 0) := by
    intro f _
    ext u'
    by_cases hf_eq : f = fld
    · subst hf_eq
      simp only [↓reduceIte]
      by_cases hu_eq : u' = u
      · subst hu_eq
        simp only [hu, ↓reduceIte, Function.update_self]
        exact readPacked_writePacked_self _ _ _ mem _ hval
      · simp only [Function.update_of_ne hu_eq]
        split_ifs with hu'
        · exact readPacked_writePacked_of_ne hw mem (by omega) val
        · rfl
    · simp only [hf_eq, ↓reduceIte]
      split_ifs with hu'
      · exact readPacked_writePacked_of_ne hw mem (by omega) val
      · rfl
  refine ⟨?_, fun addr ha => houtN addr fun hn => ha (Or.inr (Or.inl hn))⟩
  have h0 := hupd_f 0 (by decide); simp only [Nat.add_zero] at h0
  have h1 := hupd_f 1 (by decide)
  have h2 := hupd_f 2 (by decide)
  have h3 := hupd_f 3 (by decide)
  have hchild_eq : (extractBufTrie L mem').trieChild = tr.trieChild := by
    ext v ch; dsimp only [extractBufTrie, tr]
    split_ifs with hv
    · exact hc_eq _ (child_idx_lt hv.1 hv.2)
    · rfl
  have hna_eq : (extractBufTrie L mem').nodeAlloc = tr.nodeAlloc := hi_eq (6 * L.qMax) (by omega)
  have hia_eq : (extractBufTrie L mem').itemAlloc = tr.itemAlloc :=
    hi_eq (6 * L.qMax + 1) (by omega)
  have hil0 : (extractBufTrie L mem').itemLeaf = tr.itemLeaf := by
    ext id; dsimp only [extractBufTrie, tr]
    split_ifs with hid
    · exact hi_eq (6 * id) (by omega)
    · rfl
  have hil1 : (extractBufTrie L mem').itemBucket = tr.itemBucket := by
    ext id; dsimp only [extractBufTrie, tr]
    split_ifs with hid
    · exact hi_eq (6 * id + 1) (by omega)
    · rfl
  have hil2 : (extractBufTrie L mem').itemLoc = tr.itemLoc := by
    ext id; dsimp only [extractBufTrie, tr]
    split_ifs with hid
    · exact hi_eq (6 * id + 2) (by omega)
    · rfl
  rcases fld with _ | _ | _ | _ | _ <;> try omega
  all_goals (
    simp only [↓reduceIte, Nat.reduceEqDiff] at h0 h1 h2 h3
    dsimp only [tr, extractBufTrie] at hna_eq hia_eq hchild_eq hil0 hil1 hil2 ⊢
    congr 1)

private theorem extractBufTrie_writeItemField {L : TrieLayout} {mem : ℕ → ℕ} {id fld val : ℕ}
    (hvL : L.Valid L.w (L.metaBase + L.offItem + packedWords (6 * L.qMax + 6) L.ptrB L.w))
    (hid : id < L.qMax) (hfld : fld < 3) (hval : val < 2 ^ L.ptrB) :
    let tr := extractBufTrie L mem
    let mem' := writePacked (L.metaBase + L.offItem) L.ptrB L.w mem (6 * id + fld) val
    extractBufTrie L mem' =
      (match fld with
       | 0 => { tr with itemLeaf := Function.update tr.itemLeaf id val }
       | 1 => { tr with itemBucket := Function.update tr.itemBucket id val }
       | _ => { tr with itemLoc := Function.update tr.itemLoc id val }) ∧
      ∀ addr, ¬L.OwnsAddr addr → mem' addr = mem addr := by
  intro tr mem'
  obtain ⟨hw, _, _, _, _, _, _, _, _, _, _, _, _, hd1, hd2, _⟩ := hvL
  have hidx : 6 * id + fld < 6 * L.qMax + 6 := by omega
  have houtI : ∀ addr, ¬(L.metaBase + L.offItem ≤ addr ∧
      addr < L.metaBase + L.offItem + packedWords (6 * L.qMax + 6) L.ptrB L.w) →
      mem' addr = mem addr := fun addr ha => writePacked_outside hw mem hidx val ha
  have hc_eq : ∀ idx < L.maxNodes * 2 ^ L.bChar,
      readPacked (L.metaBase + L.offChild) L.ptrB L.w mem' idx =
        readPacked (L.metaBase + L.offChild) L.ptrB L.w mem idx := fun idx hi =>
    readPacked_congr hw (fun addr ha => houtI addr (by omega)) hi
  have hn_eq : ∀ idx < 6 * L.maxNodes,
      readPacked (L.metaBase + L.offNode) L.ptrB L.w mem' idx =
        readPacked (L.metaBase + L.offNode) L.ptrB L.w mem idx := fun idx hi =>
    readPacked_congr hw (fun addr ha => houtI addr (by omega)) hi
  have hupd_f : ∀ f < 3,
      (fun i => if i < L.qMax then
        readPacked (L.metaBase + L.offItem) L.ptrB L.w mem' (6 * i + f) else 0) =
      if f = fld then
        Function.update (fun i => if i < L.qMax then
          readPacked (L.metaBase + L.offItem) L.ptrB L.w mem (6 * i + f) else 0) id val
      else
        (fun i => if i < L.qMax then
          readPacked (L.metaBase + L.offItem) L.ptrB L.w mem (6 * i + f) else 0) := by
    intro f _
    ext i
    by_cases hf_eq : f = fld
    · subst hf_eq
      simp only [↓reduceIte]
      by_cases hi_eq : i = id
      · subst hi_eq
        simp only [hid, ↓reduceIte, Function.update_self]
        exact readPacked_writePacked_self _ _ _ mem _ hval
      · simp only [Function.update_of_ne hi_eq]
        split_ifs with hi'
        · exact readPacked_writePacked_of_ne hw mem (by omega) val
        · rfl
    · simp only [hf_eq, ↓reduceIte]
      split_ifs with hi'
      · exact readPacked_writePacked_of_ne hw mem (by omega) val
      · rfl
  refine ⟨?_, fun addr ha => houtI addr fun hi => ha (Or.inr (Or.inr hi))⟩
  have h0 := hupd_f 0 (by decide); simp only [Nat.add_zero] at h0
  have h1 := hupd_f 1 (by decide)
  have h2 := hupd_f 2 (by decide)
  have hna_eq : (extractBufTrie L mem').nodeAlloc = tr.nodeAlloc :=
    readPacked_writePacked_of_ne hw mem (by omega) val
  have hia_eq : (extractBufTrie L mem').itemAlloc = tr.itemAlloc :=
    readPacked_writePacked_of_ne hw mem (by omega) val
  have hchild_eq : (extractBufTrie L mem').trieChild = tr.trieChild := by
    ext v ch; dsimp only [extractBufTrie, tr]
    split_ifs with hv
    · exact hc_eq _ (child_idx_lt hv.1 hv.2)
    · rfl
  have hnp : (extractBufTrie L mem').nodeParent = tr.nodeParent := by
    ext u; dsimp only [extractBufTrie, tr]
    split_ifs with hu
    · exact hn_eq _ (by omega)
    · rfl
  have hnc : (extractBufTrie L mem').nodeChar = tr.nodeChar := by
    ext u; dsimp only [extractBufTrie, tr]
    split_ifs with hu
    · exact hn_eq _ (by omega)
    · rfl
  have hnl : (extractBufTrie L mem').nodeLeafItem = tr.nodeLeafItem := by
    ext u; dsimp only [extractBufTrie, tr]
    split_ifs with hu
    · exact hn_eq _ (by omega)
    · rfl
  have hna : (extractBufTrie L mem').nodeActive = tr.nodeActive := by
    ext u; dsimp only [extractBufTrie, tr]
    split_ifs with hu
    · exact hn_eq _ (by omega)
    · rfl
  rcases fld with _ | _ | _ | _ <;> try omega
  all_goals (
    simp only [↓reduceIte, Nat.reduceEqDiff] at h0 h1 h2
    dsimp only [tr, extractBufTrie] at hna_eq hia_eq hchild_eq hnp hnc hnl hna ⊢
    congr 1)

private theorem extractBufTrie_writeHeader {L : TrieLayout} {mem : ℕ → ℕ} {isItem val : ℕ}
    (hvL : L.Valid L.w (L.metaBase + L.offItem + packedWords (6 * L.qMax + 6) L.ptrB L.w))
    (his : isItem < 2) (hval : val < 2 ^ L.ptrB) :
    let tr := extractBufTrie L mem
    let mem' := writePacked (L.metaBase + L.offItem) L.ptrB L.w mem (6 * L.qMax + isItem) val
    extractBufTrie L mem' =
      (if isItem = 0 then { tr with nodeAlloc := val } else { tr with itemAlloc := val }) ∧
      ∀ addr, ¬L.OwnsAddr addr → mem' addr = mem addr := by
  intro tr mem'
  obtain ⟨hw, _, _, _, _, _, _, _, _, _, _, _, _, hd1, hd2, _⟩ := hvL
  have hidx : 6 * L.qMax + isItem < 6 * L.qMax + 6 := by omega
  have houtI : ∀ addr, ¬(L.metaBase + L.offItem ≤ addr ∧
      addr < L.metaBase + L.offItem + packedWords (6 * L.qMax + 6) L.ptrB L.w) →
      mem' addr = mem addr := fun addr ha => writePacked_outside hw mem hidx val ha
  have hc_eq : ∀ idx < L.maxNodes * 2 ^ L.bChar,
      readPacked (L.metaBase + L.offChild) L.ptrB L.w mem' idx =
        readPacked (L.metaBase + L.offChild) L.ptrB L.w mem idx := fun idx hi =>
    readPacked_congr hw (fun addr ha => houtI addr (by omega)) hi
  have hn_eq : ∀ idx < 6 * L.maxNodes,
      readPacked (L.metaBase + L.offNode) L.ptrB L.w mem' idx =
        readPacked (L.metaBase + L.offNode) L.ptrB L.w mem idx := fun idx hi =>
    readPacked_congr hw (fun addr ha => houtI addr (by omega)) hi
  refine ⟨?_, fun addr ha => houtI addr fun hi => ha (Or.inr (Or.inr hi))⟩
  have hchild_eq : (extractBufTrie L mem').trieChild = tr.trieChild := by
    ext v ch; dsimp only [extractBufTrie, tr]
    split_ifs with hv
    · exact hc_eq _ (child_idx_lt hv.1 hv.2)
    · rfl
  have hnp : (extractBufTrie L mem').nodeParent = tr.nodeParent := by
    ext u; dsimp only [extractBufTrie, tr]
    split_ifs with hu
    · exact hn_eq _ (by omega)
    · rfl
  have hnc : (extractBufTrie L mem').nodeChar = tr.nodeChar := by
    ext u; dsimp only [extractBufTrie, tr]
    split_ifs with hu
    · exact hn_eq _ (by omega)
    · rfl
  have hnl : (extractBufTrie L mem').nodeLeafItem = tr.nodeLeafItem := by
    ext u; dsimp only [extractBufTrie, tr]
    split_ifs with hu
    · exact hn_eq _ (by omega)
    · rfl
  have hna : (extractBufTrie L mem').nodeActive = tr.nodeActive := by
    ext u; dsimp only [extractBufTrie, tr]
    split_ifs with hu
    · exact hn_eq _ (by omega)
    · rfl
  have hi0 : (extractBufTrie L mem').itemLeaf = tr.itemLeaf := by
    ext i; dsimp only [extractBufTrie, tr]
    split_ifs with hi'
    · exact readPacked_writePacked_of_ne hw mem (by omega) val
    · rfl
  have hi1 : (extractBufTrie L mem').itemBucket = tr.itemBucket := by
    ext i; dsimp only [extractBufTrie, tr]
    split_ifs with hi'
    · exact readPacked_writePacked_of_ne hw mem (by omega) val
    · rfl
  have hi2 : (extractBufTrie L mem').itemLoc = tr.itemLoc := by
    ext i; dsimp only [extractBufTrie, tr]
    split_ifs with hi'
    · exact readPacked_writePacked_of_ne hw mem (by omega) val
    · rfl
  rcases isItem with _ | _ | _ <;> try omega
  · simp only [↓reduceIte]
    have hna_s : (extractBufTrie L mem').nodeAlloc = val := by
      dsimp only [extractBufTrie, mem']
      simpa only [Nat.add_zero] using readPacked_writePacked_self _ _ _ mem (6 * L.qMax) hval
    have hia_s : (extractBufTrie L mem').itemAlloc = tr.itemAlloc := by
      dsimp only [extractBufTrie, tr, mem']
      exact readPacked_writePacked_of_ne hw mem (by omega) val
    dsimp only [tr, extractBufTrie] at hna_s hia_s hchild_eq hnp hnc hnl hna hi0 hi1 hi2 ⊢
    congr 1
  · simp only [Nat.succ_ne_zero, ↓reduceIte]
    have hna_s : (extractBufTrie L mem').nodeAlloc = tr.nodeAlloc := by
      dsimp only [extractBufTrie, tr, mem']
      exact readPacked_writePacked_of_ne hw mem (by omega) val
    have hia_s : (extractBufTrie L mem').itemAlloc = val := by
      dsimp only [extractBufTrie, mem']
      exact readPacked_writePacked_self _ _ _ mem (6 * L.qMax + 1) hval
    dsimp only [tr, extractBufTrie] at hna_s hia_s hchild_eq hnp hnc hnl hna hi0 hi1 hi2 ⊢
    congr 1

/-! ## Section 3: `Memory.Prog` Implementations & `RealizesBounded .exact` -/

/-- Allocation-bound invariant on `BufTrie` fields exposed across `module` boundaries
(`ValidBufTrie` in `SuccinctWhpBufferTrie` is abstract). -/
@[expose] def RawBufTrieBounds (tr : BufTrie) : Prop :=
  1 ≤ tr.nodeAlloc ∧
  (∀ v c, tr.trieChild v c ≠ 0 → tr.trieChild v c < tr.nodeAlloc) ∧
  (∀ u < tr.nodeAlloc, tr.nodeLeafItem u ≠ 0 → tr.nodeLeafItem u ≤ tr.itemAlloc)

/-- Parent-log clearing invariant exposed across `module` boundaries (`ClearableBufTrie` in
`SuccinctWhpBufferTrie` is abstract), sufficient to re-establish `RawBufTrieBounds` once
`bufClearSteps k` finishes (`k ≥ tr.nodeAlloc`). -/
@[expose] def RawClearableBounds (tr : BufTrie) : Prop :=
  1 ≤ tr.nodeAlloc ∧
  (∀ u, tr.nodeAlloc ≤ u → tr.nodeLeafItem u = 0) ∧
  (∀ u, 1 ≤ u → u < tr.nodeAlloc →
    tr.nodeParent u < u ∧ tr.trieChild (tr.nodeParent u) (tr.nodeChar u) = u) ∧
  (∀ v ch, tr.trieChild v ch ≠ 0 →
    1 ≤ tr.trieChild v ch ∧ tr.trieChild v ch < tr.nodeAlloc ∧
    tr.nodeParent (tr.trieChild v ch) = v ∧ tr.nodeChar (tr.trieChild v ch) = ch)

theorem rawBufTrieBounds_empty : RawBufTrieBounds emptyBufTrie :=
  ⟨le_rfl, fun _ _ h => absurd rfl h, fun _ _ h => absurd rfl h⟩

theorem rawClearableBounds_empty : RawClearableBounds emptyBufTrie :=
  ⟨le_rfl, fun _ _ => rfl, fun _ h1 h2 => by dsimp only [emptyBufTrie] at h2; omega,
    fun _ _ h => absurd rfl h⟩

theorem RawBufTrieBounds.delete (cTab bChar rKey : ℕ) {tr : BufTrie}
    (hb : RawBufTrieBounds tr) : RawBufTrieBounds (bufDelete cTab bChar tr rKey) := by
  unfold bufDelete
  cases bufWalk bChar tr.trieChild rKey cTab 0 0 with
  | none => exact hb
  | some leaf =>
    dsimp only
    split_ifs <;> exact hb

theorem RawClearableBounds.delete (cTab bChar rKey : ℕ) {tr : BufTrie}
    (hc : RawClearableBounds tr) : RawClearableBounds (bufDelete cTab bChar tr rKey) := by
  unfold bufDelete
  cases bufWalk bChar tr.trieChild rKey cTab 0 0 with
  | none => exact hc
  | some leaf =>
    dsimp only
    split_ifs <;> exact hc

private theorem bufEnsurePath_raw_pres (bChar rKey : ℕ) :
    ∀ m off (tr : BufTrie) (cur : ℕ),
      cur < tr.nodeAlloc →
      RawBufTrieBounds tr →
      RawClearableBounds tr →
      let p := bufEnsurePath bChar rKey m off tr cur
      p.2 < p.1.nodeAlloc ∧
      p.1.itemAlloc = tr.itemAlloc ∧
      RawBufTrieBounds p.1 ∧
      RawClearableBounds p.1 := by
  intro m
  induction m with
  | zero =>
    intro _ tr cur hcur hb hc
    exact ⟨hcur, rfl, hb, hc⟩
  | succ m ih =>
    intro off tr cur hcur hb hc
    dsimp only [bufEnsurePath]
    set ch := laneGet bChar rKey off
    by_cases h0 : tr.trieChild cur ch = 0
    · simp only [h0, ↓reduceIte]
      set u := tr.nodeAlloc
      set tr1 : BufTrie :=
        { tr with
          nodeAlloc := u + 1
          trieChild := Function.update tr.trieChild cur (Function.update (tr.trieChild cur) ch u)
          nodeParent := Function.update tr.nodeParent u cur
          nodeChar := Function.update tr.nodeChar u ch
          nodeLeafItem := Function.update tr.nodeLeafItem u 0 }
      have hu_pos : 1 ≤ u := hb.1
      have hb1 : RawBufTrieBounds tr1 := by
        refine ⟨by dsimp only [tr1]; omega, ?_, ?_⟩
        · intro v c hnz; dsimp only [tr1] at hnz ⊢
          by_cases hv : v = cur
          · subst hv
            by_cases hcc : c = ch
            · subst hcc; simp only [Function.update_self]; omega
            · simp only [Function.update_self, Function.update_of_ne hcc] at hnz ⊢
              exact (hb.2.1 v c hnz).trans (Nat.lt_succ_self u)
          · simp only [Function.update_of_ne hv] at hnz ⊢
            exact (hb.2.1 v c hnz).trans (Nat.lt_succ_self u)
        · intro w hw hnz; dsimp only [tr1] at hw hnz ⊢
          by_cases hwu : w = u
          · subst hwu; simp only [Function.update_self] at hnz; exact absurd rfl hnz
          · rw [Function.update_of_ne hwu] at hnz ⊢
            exact hb.2.2 w (by omega) hnz
      have hc1 : RawClearableBounds tr1 := by
        refine ⟨by dsimp only [tr1]; omega, ?_, ?_, ?_⟩
        · intro w hw; dsimp only [tr1] at hw ⊢
          rw [Function.update_of_ne (by omega)]
          exact hc.2.1 w (by omega)
        · intro w hw1 hw_lt; dsimp only [tr1] at hw_lt ⊢
          by_cases hwu : w = u
          · subst hwu
            simp only [Function.update_self]
            exact ⟨hcur, trivial⟩
          · have hw_old : w < u := by omega
            obtain ⟨hp_w, hch_w⟩ := hc.2.2.1 w hw1 hw_old
            rw [Function.update_of_ne hwu, Function.update_of_ne hwu]
            refine ⟨hp_w, ?_⟩
            by_cases hvp : tr.nodeParent w = cur
            · by_cases hvc : tr.nodeChar w = ch
              · rw [hvp, hvc, h0] at hch_w; omega
              · rw [hvp] at hch_w ⊢
                simp only [Function.update_self, Function.update_of_ne hvc, hch_w]
            · simp only [Function.update_of_ne hvp, hch_w]
        · intro v c hnz; dsimp only [tr1] at hnz ⊢
          by_cases hv : v = cur
          · subst hv
            by_cases hcc : c = ch
            · subst hcc
              simp only [Function.update_self]
              exact ⟨hu_pos, Nat.lt_succ_self u, trivial, trivial⟩
            · simp only [Function.update_self, Function.update_of_ne hcc] at hnz ⊢
              obtain ⟨h1, h2, h3, h4⟩ := hc.2.2.2 v c hnz
              have hne : tr.trieChild v c ≠ u := Nat.ne_of_lt h2
              rw [Function.update_of_ne hne, Function.update_of_ne hne]
              exact ⟨h1, h2.trans (Nat.lt_succ_self u), h3, h4⟩
          · simp only [Function.update_of_ne hv] at hnz ⊢
            obtain ⟨h1, h2, h3, h4⟩ := hc.2.2.2 v c hnz
            have hne : tr.trieChild v c ≠ u := Nat.ne_of_lt h2
            rw [Function.update_of_ne hne, Function.update_of_ne hne]
            exact ⟨h1, h2.trans (Nat.lt_succ_self u), h3, h4⟩
      obtain ⟨hl, hia, hbp, hcp⟩ := ih (off + 1) tr1 u (Nat.lt_succ_self u) hb1 hc1
      exact ⟨hl, hia, hbp, hcp⟩
    · simp only [h0, ↓reduceIte]
      exact ih (off + 1) tr (tr.trieChild cur ch) (hb.2.1 cur ch h0) hb hc

theorem RawBufTrieBounds.insert_and_clearable (cTab bChar rKey bkt loc : ℕ) {tr : BufTrie}
    (hb : RawBufTrieBounds tr) (hc : RawClearableBounds tr) :
    RawBufTrieBounds (bufInsert cTab bChar tr rKey bkt loc) ∧
    RawClearableBounds (bufInsert cTab bChar tr rKey bkt loc) := by
  obtain ⟨hleaf_lt, _, hb1, hc1⟩ := bufEnsurePath_raw_pres bChar rKey cTab 0 tr 0 hb.1 hb hc
  unfold bufInsert
  dsimp only
  set p := bufEnsurePath bChar rKey cTab 0 tr 0
  have hlt_p : p.2 < p.1.nodeAlloc := hleaf_lt
  by_cases hid0 : p.1.nodeLeafItem p.2 = 0
  · simp only [hid0, ↓reduceIte]
    refine ⟨⟨hb1.1, hb1.2.1, ?_⟩, ⟨hc1.1, ?_, hc1.2.2.1, hc1.2.2.2⟩⟩
    · intro w hw hnz; dsimp only at hw hnz ⊢
      by_cases hwl : w = p.2
      · subst hwl; simp only [Function.update_self]; exact le_rfl
      · rw [Function.update_of_ne hwl] at hnz ⊢
        exact (hb1.2.2 w hw hnz).trans (Nat.le_succ _)
    · intro w hw; dsimp only at hw ⊢
      rw [Function.update_of_ne (by omega)]
      exact hc1.2.1 w hw
  · simp only [hid0, ↓reduceIte]
    exact ⟨hb1, hc1⟩

theorem RawClearableBounds.clearOne_step {tr : BufTrie} (hc : RawClearableBounds tr) :
    RawClearableBounds (bufClearOne tr) ∧
    (bufClearOne tr).nodeAlloc = max 1 (tr.nodeAlloc - 1) := by
  obtain ⟨halloc, hzero, hedge, hchild⟩ := hc
  dsimp only [bufClearOne]
  by_cases hgt : 1 < tr.nodeAlloc
  · simp only [hgt, ↓reduceIte]
    set u := tr.nodeAlloc - 1
    set p := tr.nodeParent u
    set ch := tr.nodeChar u
    refine ⟨⟨by dsimp only; omega, ?_, ?_, ?_⟩, by omega⟩
    · intro w hw_ge; dsimp only at hw_ge ⊢
      by_cases hw_eq : w = u
      · subst hw_eq; simp only [Function.update_self]
      · rw [Function.update_of_ne hw_eq]; exact hzero w (by omega)
    · intro w hw1 hw_lt; dsimp only at hw_lt ⊢
      obtain ⟨hp_w, hc_w⟩ := hedge w hw1 (by omega)
      refine ⟨hp_w, ?_⟩
      by_cases hvp : tr.nodeParent w = p
      · by_cases hvc : tr.nodeChar w = ch
        · have hu_eq : tr.trieChild p ch = u := (hedge u (by omega) (by omega)).2
          have hw_eq_u : w = u := by rw [← hc_w, hvp, hvc, hu_eq]
          omega
        · rw [hvp] at hc_w ⊢
          simp only [Function.update_self, Function.update_of_ne hvc, hc_w]
      · simp only [Function.update_of_ne hvp, hc_w]
    · intro v c hnz; dsimp only at hnz ⊢
      by_cases hv : v = p
      · subst hv
        by_cases hcc : c = ch
        · subst hcc; simp only [Function.update_self] at hnz; exact absurd rfl hnz
        · simp only [Function.update_self, Function.update_of_ne hcc] at hnz ⊢
          obtain ⟨h1, h2, h3, h4⟩ := hchild p c hnz
          have hne_u : tr.trieChild p c ≠ u := fun heq => hcc (by rw [← h4, heq])
          exact ⟨h1, by omega, h3, h4⟩
      · simp only [Function.update_of_ne hv] at hnz ⊢
        obtain ⟨h1, h2, h3, h4⟩ := hchild v c hnz
        have hne_u : tr.trieChild v c ≠ u := fun heq => hv (by rw [← h3, heq])
        exact ⟨h1, by omega, h3, h4⟩
  · simp only [hgt, ↓reduceIte]
    refine ⟨⟨le_rfl, ?_, fun _ h1 h2 => by dsimp only at h2; omega, ?_⟩, by omega⟩
    · intro w hw_ge; dsimp only at hw_ge ⊢
      rw [Function.update_of_ne (by omega)]; exact hzero w (by omega)
    · intro v c hnz; dsimp only at hnz; obtain ⟨h1, h2, _⟩ := hchild v c hnz; omega

theorem RawClearableBounds.clearSteps_bounds :
    ∀ (k : ℕ) {tr : BufTrie},
      RawClearableBounds tr →
      tr.nodeAlloc ≤ k →
      RawBufTrieBounds (bufClearSteps k tr) ∧
      RawClearableBounds (bufClearSteps k tr) := by
  intro k
  induction k with
  | zero => intro tr hc hle; have := hc.1; omega
  | succ k ih =>
    intro tr hc hle
    dsimp only [bufClearSteps]
    by_cases ha1 : tr.nodeAlloc = 1
    · have hgt : ¬(1 < tr.nodeAlloc) := by omega
      obtain ⟨hc1, hna1⟩ := hc.clearOne_step
      have hna1_eq : (bufClearOne tr).nodeAlloc = 1 := by rw [hna1]; omega
      cases k with
      | zero =>
        dsimp only [bufClearSteps]
        refine ⟨⟨by rw [hna1_eq], ?_, ?_⟩, hc1⟩
        · intro v c hnz; obtain ⟨h1, h2, _⟩ := hc1.2.2.2 v c hnz; omega
        · intro u hu hnz
          have hu0 : u = 0 := by omega
          subst hu0
          dsimp only [bufClearOne] at hnz
          simp only [hgt, ↓reduceIte] at hnz
          rw [Function.update_self] at hnz
          exact absurd rfl hnz
      | succ k' => exact ih hc1 (by omega)
    · obtain ⟨hc1, hna1⟩ := hc.clearOne_step
      have := hc.1
      exact ih hc1 (by omega)

/-- One step of `bufWalk` in `Memory.Prog`: given `(ctx, ((found, cur), remKey))`, advances one
`bChar`-bit digit when `found ≠ 0` and `cur < maxNodes` (`1 ≤ memoryCost` unconditionally). -/
private def bufWalkStepProg : TrieCtx × ((ℕ × ℕ) × ℕ) → Memory.Prog ((ℕ × ℕ) × ℕ)
  | ((((mb, oc), (_on, _oi)), ((pb, wv), ((_ct, bc), (mn, _qm)))), ((found, cur), remKey)) => do
    let mask ← pure ((1 <<< bc) - 1)
    let ch ← pure (remKey &&& mask)
    let idx ← if cur < mn then pure ((cur <<< bc) + ch) else pure 0
    let nxt ← readPackedCompGenProg (((mb, oc), (pb, wv)), idx)
    if found = 0 then pure ((0, 0), 0)
    else if cur < mn then
      if nxt = 0 then pure ((0, 0), 0)
      else pure ((1, nxt), remKey >>> bc)
    else pure ((0, 0), 0)

private theorem memoryCost_bufWalkStepProg_pos (x : TrieCtx × ((ℕ × ℕ) × ℕ)) (s : Memory.State) :
    1 ≤ memoryCost (bufWalkStepProg x) s := by
  rcases x with ⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩
  unfold bufWalkStepProg
  simp only [pure_bind]
  split_ifs <;>
    simp only [Realization.memoryCost_bind', memoryCost_readPackedCompGenProg,
      runClient_state_readPackedCompGenProg, memoryCost_pure] <;>
    omega

private def BufWalkStepPre (w : ℕ) : TrieCtx × ((ℕ × ℕ) × ℕ) → Memory.State → Prop
  | (ctx, _st), s => (TrieLayout.ofCtx ctx).Valid w s.frontier

private theorem realizesBounded_bufWalkStep :
    RealizesBounded .exact bufWalkStepProg
      (WordEncoding.encode (α := TrieCtx × ((ℕ × ℕ) × ℕ)))
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      BufWalkStepPre (fun _ _ => 0) := by
  have hrp := realizesBounded_readPackedCompGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨mb, oc⟩, ⟨on_, oi⟩⟩, ⟨⟨pb, wv⟩, ⟨⟨ct, bc⟩, ⟨mn, qm⟩⟩⟩⟩, ⟨⟨found, cur⟩, rk⟩⟩
    dsimp only [BufWalkStepPre, TrieLayout.ofCtx] at h
    obtain ⟨hw, hwv, hpb, hbc0, hbc, _, hmn1, _, _, _, hmc, _, _, hd1, hd2, hfr⟩ := h
    subst hwv
    try dsimp only [Fits] at *
    have hpow_bc : 2 ^ bc < 2 ^ w := Nat.pow_lt_pow_right Nat.one_lt_two hbc
    have h1_lt : 1 < 2 ^ w := Nat.one_lt_two_pow hw.ne'
    have hch_lt : rk &&& (2 ^ bc - 1) < 2 ^ bc := by
      rw [Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_lt _ (Nat.two_pow_pos bc)
    try simp only [Nat.shiftLeft_eq 1, one_mul] at *)
  all_goals try exact Nat.one_le_two_pow
  all_goals try exact hpow_bc
  all_goals try exact h1_lt
  all_goals try exact ⟨mn * 2 ^ bc, hw, rfl, hpb, Nat.mul_pos hmn1 (Nat.two_pow_pos bc), by omega⟩
  all_goals (
    have hsh_lt : (cur <<< bc) + (rk &&& (2 ^ bc - 1)) < mn * 2 ^ bc :=
      child_idx_lt ‹cur < mn› hch_lt
    try exact hsh_lt.trans hmc
    try exact ⟨mn * 2 ^ bc, hw, rfl, hpb, hsh_lt, by omega⟩)

private def bufWalkLoopProg : (TrieCtx × ((ℕ × ℕ) × ℕ)) × ℕ → Memory.Prog ((ℕ × ℕ) × ℕ)
  | ((ctx, st), fuel) => iterate bufWalkStepProg ctx fuel st

private theorem realizesBounded_bufWalkLoop :
    RealizesBounded .exact bufWalkLoopProg
      (WordEncoding.encode (α := (TrieCtx × ((ℕ × ℕ) × ℕ)) × ℕ))
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (fun w ((ctx, st), fuel) s => iterationSafe bufWalkStepProg BufWalkStepPre w ctx fuel st s)
      (fun _ _ => 0) :=
  RealizesBounded.iterate₀
    (WordEncoding.encode (α := TrieCtx))
    (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
    realizesBounded_bufWalkStep
    memoryCost_bufWalkStepProg_pos

/-- Bounded `cTab`-step `bufWalk` returning `(foundFlag, leaf)`. -/
private def bufWalkBoundedProg : TrieCtx × ℕ → Memory.Prog (ℕ × ℕ)
  | (ctx, rKey) => do
    let cTab ← pure ctx.2.2.1.1
    let res ← bufWalkLoopProg ((ctx, ((1, 0), rKey)), cTab)
    pure res.1

private def BufWalkBoundedPre (w : ℕ) : TrieCtx × ℕ → Memory.State → Prop
  | (ctx, _rKey), s => (TrieLayout.ofCtx ctx).Valid w s.frontier

private theorem bufWalk_iter_spec {L : TrieLayout} {s : Memory.State}
    (hvL : L.Valid L.w s.frontier) (rKey : ℕ) :
    ∀ m off (cur : ℕ),
      iterationSafe bufWalkStepProg BufWalkStepPre L.w L.toCtx m
        ((1, cur), rKey >>> (off * L.bChar)) s ∧
      (Memory.spec 0).clientState s
        (iterate bufWalkStepProg L.toCtx m ((1, cur), rKey >>> (off * L.bChar))) = s ∧
      memoryCost (iterate bufWalkStepProg L.toCtx m ((1, cur), rKey >>> (off * L.bChar))) s ≤
        2 * m ∧
      ((Memory.spec 0).clientResult s
        (iterate bufWalkStepProg L.toCtx m ((1, cur), rKey >>> (off * L.bChar)))).1 =
        match bufWalk L.bChar (extractBufTrie L s.mem).trieChild rKey m off cur with
        | none => (0, 0)
        | some leaf => (1, leaf) := by
  have hpre0 : ∀ st, BufWalkStepPre L.w (L.toCtx, st) s := fun _ => by
    simpa only [BufWalkStepPre, TrieLayout.ofCtx_toCtx] using hvL
  have hstep_base : ∀ found cur rk,
      (Memory.spec 0).clientState s (bufWalkStepProg (L.toCtx, ((found, cur), rk))) = s ∧
      memoryCost (bufWalkStepProg (L.toCtx, ((found, cur), rk))) s ≤ 2 := by
    intro found cur rk
    unfold bufWalkStepProg
    dsimp only [TrieLayout.toCtx]
    simp only [pure_bind]
    refine ⟨?_, ?_⟩
    · unfold StateTransitionSpec.clientState
      split_ifs <;>
        simp only [prog_runClient_state_bind, prog_runClient_state_pure,
          runClient_state_readPackedCompGenProg]
      all_goals (split_ifs <;> rfl)
    · (split_ifs <;>
        simp only [Realization.memoryCost_bind', StateTransitionSpec.clientState,
          memoryCost_pure, memoryCost_readPackedCompGenProg,
          runClient_state_readPackedCompGenProg]) <;>
        (try (split_ifs <;> simp only [memoryCost_pure])) <;> omega
  have hzero_iter : ∀ m rk,
      iterationSafe bufWalkStepProg BufWalkStepPre L.w L.toCtx m ((0, 0), rk) s ∧
      (Memory.spec 0).clientState s (iterate bufWalkStepProg L.toCtx m ((0, 0), rk)) = s ∧
      memoryCost (iterate bufWalkStepProg L.toCtx m ((0, 0), rk)) s ≤ 2 * m ∧
      ((Memory.spec 0).clientResult s (iterate bufWalkStepProg L.toCtx m ((0, 0), rk))).1 =
        (0, 0) := by
    intro m
    induction m with
    | zero => intro rk; exact ⟨trivial, rfl, Nat.zero_le _, rfl⟩
    | succ m ih =>
      intro rk
      obtain ⟨hst1, hc1⟩ := hstep_base 0 0 rk
      have hres1 : (Memory.spec 0).clientResult s (bufWalkStepProg (L.toCtx, ((0, 0), rk))) =
          ((0, 0), 0) := by
        unfold bufWalkStepProg; dsimp only [TrieLayout.toCtx]
        simp only [pure_bind, ↓reduceIte]
        split_ifs <;> simp only [prog_clientResult_bind, prog_clientResult_pure,
          StateTransitionSpec.clientState, runClient_state_readPackedCompGenProg]
      obtain ⟨hs0, hst0, hc0, hr0⟩ := ih 0
      refine ⟨⟨hpre0 _, ?_⟩, ?_, ?_, ?_⟩
      · rw [hst1, hres1]; exact hs0
      · unfold iterate; rw [StateTransitionSpec.clientState_bind, hst1, hres1, hst0]
      · unfold iterate; rw [Realization.memoryCost_bind', hst1, hres1]; omega
      · unfold iterate; rw [prog_clientResult_bind, hst1, hres1]; exact hr0
  intro m
  induction m with
  | zero =>
    intro off cur
    exact ⟨trivial, rfl, Nat.zero_le _, rfl⟩
  | succ m ih =>
    intro off cur
    set rk := rKey >>> (off * L.bChar)
    have hch_eq : rk &&& ((1 <<< L.bChar) - 1) = laneGet L.bChar rKey off := by
      rw [Nat.shiftLeft_eq, one_mul]; rfl
    have hch_lt : laneGet L.bChar rKey off < 2 ^ L.bChar := laneGet_lt _ _ _
    have hrk_next : rk >>> L.bChar = rKey >>> ((off + 1) * L.bChar) := by
      dsimp only [rk]
      rw [← Nat.shiftRight_add, ← Nat.add_one_mul]
    obtain ⟨hstep_st, hstep_cost⟩ := hstep_base 1 cur rk
    by_cases hcur : cur < L.maxNodes
    · set nxt := readPacked (L.metaBase + L.offChild) L.ptrB L.w s.mem
          ((cur <<< L.bChar) + laneGet L.bChar rKey off)
      have hchild_eq : (extractBufTrie L s.mem).trieChild cur (laneGet L.bChar rKey off) = nxt := by
        simp only [extractBufTrie, hcur, hch_lt, and_self, ↓reduceIte, nxt]
      have hstep_res : (Memory.spec 0).clientResult s
          (bufWalkStepProg (L.toCtx, ((1, cur), rk))) =
          if nxt = 0 then ((0, 0), 0) else ((1, nxt), rKey >>> ((off + 1) * L.bChar)) := by
        unfold bufWalkStepProg
        dsimp only [TrieLayout.toCtx]
        simp only [Nat.one_ne_zero, ↓reduceIte, hcur, pure_bind, hch_eq, prog_clientResult_bind,
          StateTransitionSpec.clientState, clientResult_readPackedCompGenProg,
          runClient_state_readPackedCompGenProg, nxt, hrk_next]
        split_ifs <;> rfl
      by_cases hnxt0 : nxt = 0
      · obtain ⟨hs0, hst0, hc0, hr0⟩ := hzero_iter m 0
        refine ⟨⟨hpre0 _, ?_⟩, ?_, ?_, ?_⟩
        · rw [hstep_st, hstep_res, ite_eq_left hnxt0]; exact hs0
        · unfold iterate; rw [StateTransitionSpec.clientState_bind, hstep_st, hstep_res,
            ite_eq_left hnxt0, hst0]
        · unfold iterate; rw [Realization.memoryCost_bind', hstep_st, hstep_res, ite_eq_left hnxt0]
          omega
        · unfold iterate
          rw [prog_clientResult_bind, hstep_st, hstep_res, ite_eq_left hnxt0, hr0]
          simp only [bufWalk, hchild_eq, hnxt0, ↓reduceIte]
      · obtain ⟨hs1, hst1, hc1, hr1⟩ := ih (off + 1) nxt
        refine ⟨⟨hpre0 _, ?_⟩, ?_, ?_, ?_⟩
        · rw [hstep_st, hstep_res, ite_eq_right hnxt0]; exact hs1
        · unfold iterate; rw [StateTransitionSpec.clientState_bind, hstep_st, hstep_res,
            ite_eq_right hnxt0, hst1]
        · unfold iterate; rw [Realization.memoryCost_bind', hstep_st, hstep_res, ite_eq_right hnxt0]
          omega
        · unfold iterate
          rw [prog_clientResult_bind, hstep_st, hstep_res, ite_eq_right hnxt0]
          simpa only [bufWalk, hchild_eq, hnxt0, ↓reduceIte] using hr1
    · have hchild0 : (extractBufTrie L s.mem).trieChild cur (laneGet L.bChar rKey off) = 0 := by
        simp only [extractBufTrie, hcur, false_and, ↓reduceIte]
      have hstep_res : (Memory.spec 0).clientResult s
          (bufWalkStepProg (L.toCtx, ((1, cur), rk))) = ((0, 0), 0) := by
        unfold bufWalkStepProg; dsimp only [TrieLayout.toCtx]
        simp only [pure_bind, hcur, ↓reduceIte, prog_clientResult_bind, prog_clientResult_pure,
          StateTransitionSpec.clientState, runClient_state_readPackedCompGenProg, Nat.one_ne_zero]
      obtain ⟨hs0, hst0, hc0, hr0⟩ := hzero_iter m 0
      refine ⟨⟨hpre0 _, ?_⟩, ?_, ?_, ?_⟩
      · rw [hstep_st, hstep_res]; exact hs0
      · unfold iterate; rw [StateTransitionSpec.clientState_bind, hstep_st, hstep_res, hst0]
      · unfold iterate; rw [Realization.memoryCost_bind', hstep_st, hstep_res]; omega
      · unfold iterate
        rw [prog_clientResult_bind, hstep_st, hstep_res, hr0]
        simp only [bufWalk, hchild0, ↓reduceIte]

private theorem realizesBounded_bufWalkBounded :
    RealizesBounded .exact bufWalkBoundedProg
      (WordEncoding.encode (α := TrieCtx × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      BufWalkBoundedPre (fun _ _ => 0) := by
  have hloop := realizesBounded_bufWalkLoop
  realize
  all_goals (
    rcases d with ⟨ctx, rKey⟩
    have hvL : (TrieLayout.ofCtx ctx).Valid w s.frontier := h
    have hw_eq : (TrieLayout.ofCtx ctx).w = w := hvL.2.1.symm
    have hto : (TrieLayout.ofCtx ctx).toCtx = ctx := by
      rcases ctx with ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩⟩; rfl
    have hw_pos : 0 < w := hvL.1
    try exact Nat.one_lt_two_pow hw_pos.ne'
    try (
      have hct_eq : ctx.2.2.1.1 = (TrieLayout.ofCtx ctx).cTab := by
        rcases ctx with ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩⟩; rfl
      have hsafe := (bufWalk_iter_spec (L := TrieLayout.ofCtx ctx)
        (by rwa [hw_eq]) rKey (TrieLayout.ofCtx ctx).cTab 0 0).1
      rw [zero_mul, Nat.shiftRight_zero, hw_eq, hto, ← hct_eq] at hsafe
      exact hsafe))

private abbrev trieMb (c : TrieCtx) : ℕ := c.1.1.1
private abbrev trieOn (c : TrieCtx) : ℕ := c.1.2.1
private abbrev trieOi (c : TrieCtx) : ℕ := c.1.2.2
private abbrev triePb (c : TrieCtx) : ℕ := c.2.1.1
private abbrev trieWv (c : TrieCtx) : ℕ := c.2.1.2
private abbrev trieCt (c : TrieCtx) : ℕ := c.2.2.1.1
private abbrev trieMn (c : TrieCtx) : ℕ := c.2.2.2.1
private abbrev trieQm (c : TrieCtx) : ℕ := c.2.2.2.2

/-- `bufLookup` in `Memory.Prog`, returning `(foundFlag, (bkt, loc))` (`RealizesBounded .exact`,
`¬ReadsWidth`). -/
def bufLookupBoundedProg : TrieCtx × ℕ → Memory.Prog (ℕ × (ℕ × ℕ))
  | (ctx, rKey) => do
    let mb ← pure (trieMb ctx)
    let on_ ← pure (trieOn ctx)
    let oi ← pure (trieOi ctx)
    let pb ← pure (triePb ctx)
    let wv ← pure (trieWv ctx)
    let mn ← pure (trieMn ctx)
    let qm ← pure (trieQm ctx)
    let wk ← bufWalkBoundedProg (ctx, rKey)
    if wk.1 = 0 then pure (0, (0, 0))
    else if wk.2 < mn then do
      let id1 ← readPackedCompGenProg (((mb, on_), (pb, wv)), 6 * wk.2 + 2)
      let act ← readPackedCompGenProg (((mb, on_), (pb, wv)), 6 * wk.2 + 3)
      if id1 = 0 then pure (0, (0, 0))
      else if act = 0 then pure (0, (0, 0))
      else do
        let id ← pure (id1 - 1)
        if id < qm then do
          let bkt ← readPackedCompGenProg (((mb, oi), (pb, wv)), 6 * id + 1)
          let loc ← readPackedCompGenProg (((mb, oi), (pb, wv)), 6 * id + 2)
          pure (1, (bkt, loc))
        else pure (1, (0, 0))
    else pure (0, (0, 0))

/-- Precondition for `bufLookupBoundedProg`. -/
@[expose] def BufLookupPre (w : ℕ) : TrieCtx × ℕ → Memory.State → Prop
  | (ctx, _rKey), s => (TrieLayout.ofCtx ctx).Valid w s.frontier

theorem realizesBounded_bufLookup :
    RealizesBounded .exact bufLookupBoundedProg
      (WordEncoding.encode (α := TrieCtx × ℕ))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      BufLookupPre (fun _ _ => 0) := by
  have hwk := realizesBounded_bufWalkBounded
  have hrp := realizesBounded_readPackedCompGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨mb, oc⟩, ⟨on_, oi⟩⟩, ⟨⟨pb, wv⟩, ⟨⟨ct, bc⟩, ⟨mn, qm⟩⟩⟩⟩, rKey⟩
    dsimp only [BufLookupPre, TrieLayout.ofCtx] at h
    obtain ⟨hw, hwv, hpb, hbc0, hbc, hbc_pb, hmn1, hmn_pb, hqm_pb, hct_w, hmc, h6m, h6q,
      hd1, hd2, hfr⟩ := h
    subst hwv
    have hvL0 : (TrieLayout.mk mb oc on_ oi pb w ct bc mn qm).Valid w s.frontier :=
      ⟨hw, rfl, hpb, hbc0, hbc, hbc_pb, hmn1, hmn_pb, hqm_pb, hct_w, hmc, h6m, h6q,
        hd1, hd2, hfr⟩
    try dsimp only [Fits, trieMb, trieOn, trieOi, triePb, trieWv, trieCt, trieMn, trieQm] at *
    have hw_st : (Memory.spec 0).clientState s
        (bufWalkBoundedProg ((((mb, oc), (on_, oi)), ((pb, w), ((ct, bc), (mn, qm)))), rKey)) =
        s := by
      unfold bufWalkBoundedProg bufWalkLoopProg
      dsimp only
      have hst_it := (bufWalk_iter_spec hvL0 rKey ct 0 0).2.1
      rw [zero_mul, Nat.shiftRight_zero] at hst_it
      dsimp only [TrieLayout.toCtx] at hst_it
      rw [pure_bind, StateTransitionSpec.clientState_bind, hst_it]
      rfl
    try simp only [StateTransitionSpec.clientState, hw_st, runClient_state_readPackedCompGenProg]
      at *
    have h1_lt : 1 < 2 ^ w := Nat.one_lt_two_pow hw.ne')
  all_goals try exact hvL0
  all_goals try exact h1_lt
  all_goals try (refine ⟨6 * mn, hw, rfl, hpb, by omega, by omega⟩)
  all_goals try (refine ⟨6 * qm + 6, hw, rfl, hpb, by omega, by omega⟩)
  all_goals omega

theorem bufLookupBoundedProg_spec {L : TrieLayout} {s : Memory.State}
    (hvL : L.Valid L.w s.frontier)
    {mapFn : ℕ → Option (ℕ × ℕ)}
    (hv : ValidBufTrie L.cTab L.bChar (extractBufTrie L s.mem) mapFn)
    {rKey : ℕ} (hk : rKey < 2 ^ (L.cTab * L.bChar)) :
    (Memory.spec 0).clientState s (bufLookupBoundedProg (L.toCtx, rKey)) = s ∧
    memoryCost (bufLookupBoundedProg (L.toCtx, rKey)) s ≤ 2 * L.cTab + 8 ∧
    (Memory.spec 0).clientResult s (bufLookupBoundedProg (L.toCtx, rKey)) =
      match mapFn rKey with
      | none => (0, (0, 0))
      | some (b, loc) => (1, (b, loc)) := by
  obtain ⟨_, hst_w, hc_w, hr_w⟩ := bufWalk_iter_spec hvL rKey L.cTab 0 0
  rw [zero_mul, Nat.shiftRight_zero] at hst_w hc_w hr_w
  have hct_proj : L.toCtx.2.2.1.1 = L.cTab := rfl
  have hw_st : (Memory.spec 0).clientState s (bufWalkBoundedProg (L.toCtx, rKey)) = s := by
    unfold bufWalkBoundedProg bufWalkLoopProg; dsimp only
    rw [hct_proj, pure_bind, StateTransitionSpec.clientState_bind, hst_w]; rfl
  have hw_cost : memoryCost (bufWalkBoundedProg (L.toCtx, rKey)) s ≤ 2 * L.cTab := by
    unfold bufWalkBoundedProg bufWalkLoopProg; dsimp only
    rw [hct_proj, pure_bind, Realization.memoryCost_bind', hst_w, memoryCost_pure, add_zero]
    exact hc_w
  have hw_res : (Memory.spec 0).clientResult s (bufWalkBoundedProg (L.toCtx, rKey)) =
      match bufWalk L.bChar (extractBufTrie L s.mem).trieChild rKey L.cTab 0 0 with
      | none => (0, 0)
      | some leaf => (1, leaf) := by
    unfold bufWalkBoundedProg bufWalkLoopProg; dsimp only
    rw [hct_proj, pure_bind, prog_clientResult_bind, hst_w, prog_clientResult_pure]
    exact hr_w
  rw [← hv.lookup_eq hk]
  unfold bufLookupBoundedProg bufLookup
  dsimp only [trieMb, trieOn, trieOi, triePb, trieWv, trieCt, trieMn, trieQm]
  simp only [pure_bind]
  have hp1 : L.toCtx.1.1.1 = L.metaBase := rfl
  have hp2 : L.toCtx.1.2.1 = L.offNode := rfl
  have hp3 : L.toCtx.1.2.2 = L.offItem := rfl
  have hp4 : L.toCtx.2.1.1 = L.ptrB := rfl
  have hp5 : L.toCtx.2.1.2 = L.w := rfl
  have hp6 : L.toCtx.2.2.2.1 = L.maxNodes := rfl
  have hp7 : L.toCtx.2.2.2.2 = L.qMax := rfl
  rw [hp1, hp2, hp3, hp4, hp5, hp6, hp7]
  cases hwalk : bufWalk L.bChar (extractBufTrie L s.mem).trieChild rKey L.cTab 0 0 with
  | none =>
    rw [hwalk] at hw_res
    refine ⟨?_, ?_, ?_⟩
    · rw [StateTransitionSpec.clientState_bind, hw_st, hw_res]; rfl
    · rw [Realization.memoryCost_bind', hw_st, hw_res]
      simp only [↓reduceIte, memoryCost_pure]; omega
    · rw [prog_clientResult_bind, hw_st, hw_res]; rfl
  | some leaf =>
    rw [hwalk] at hw_res
    by_cases hleaf : leaf < L.maxNodes
    · set id1 := readPacked (L.metaBase + L.offNode) L.ptrB L.w s.mem (6 * leaf + 2)
      set act := readPacked (L.metaBase + L.offNode) L.ptrB L.w s.mem (6 * leaf + 3)
      have hli_eq : (extractBufTrie L s.mem).nodeLeafItem leaf = id1 := by
        simp only [extractBufTrie, hleaf, ↓reduceIte, id1]
      have hact_eq : (extractBufTrie L s.mem).nodeActive leaf = act := by
        simp only [extractBufTrie, hleaf, ↓reduceIte, act]
      by_cases hid1 : id1 = 0
      · refine ⟨?_, ?_, ?_⟩
        · rw [StateTransitionSpec.clientState_bind, hw_st, hw_res]; simp [hleaf, id1, hid1]
        · rw [Realization.memoryCost_bind', hw_st, hw_res]
          simp only [Nat.one_ne_zero, ↓reduceIte, hleaf, StateTransitionSpec.clientState,
            Realization.memoryCost_bind', memoryCost_readPackedCompGenProg,
            runClient_state_readPackedCompGenProg, clientResult_readPackedCompGenProg,
            id1, hid1, memoryCost_pure]
          omega
        · rw [prog_clientResult_bind, hw_st, hw_res]; simp [hleaf, hli_eq, id1, hid1]
      · by_cases hact : act = 0
        · refine ⟨?_, ?_, ?_⟩
          · rw [StateTransitionSpec.clientState_bind, hw_st, hw_res]
            simp [hleaf, id1, hid1, act, hact]
          · rw [Realization.memoryCost_bind', hw_st, hw_res]
            simp only [Nat.one_ne_zero, ↓reduceIte, hleaf, StateTransitionSpec.clientState,
              Realization.memoryCost_bind', memoryCost_readPackedCompGenProg,
              runClient_state_readPackedCompGenProg, clientResult_readPackedCompGenProg,
              id1, hid1, act, hact, memoryCost_pure]
            omega
          · rw [prog_clientResult_bind, hw_st, hw_res]
            simp [hleaf, hli_eq, hact_eq, id1, hid1, act, hact]
        · by_cases hid_lt : id1 - 1 < L.qMax
          · refine ⟨?_, ?_, ?_⟩
            · rw [StateTransitionSpec.clientState_bind, hw_st, hw_res]
              simp [hleaf, id1, hid1, act, hact, hid_lt]
            · rw [Realization.memoryCost_bind', hw_st, hw_res]
              simp only [Nat.one_ne_zero, ↓reduceIte, hleaf, StateTransitionSpec.clientState,
                Realization.memoryCost_bind', memoryCost_readPackedCompGenProg,
                runClient_state_readPackedCompGenProg, clientResult_readPackedCompGenProg,
                id1, hid1, act, hact, hid_lt, memoryCost_pure]
              omega
            · rw [prog_clientResult_bind, hw_st, hw_res]
              simp only [Nat.one_ne_zero, ↓reduceIte, hleaf, prog_clientResult_bind,
                prog_clientResult_pure, StateTransitionSpec.clientState,
                runClient_state_readPackedCompGenProg, clientResult_readPackedCompGenProg,
                id1, hid1, act, hact, hid_lt, hli_eq, hact_eq]
              simp [extractBufTrie, id1, hid_lt]
          · refine ⟨?_, ?_, ?_⟩
            · rw [StateTransitionSpec.clientState_bind, hw_st, hw_res]
              simp [hleaf, id1, hid1, act, hact, hid_lt]
            · rw [Realization.memoryCost_bind', hw_st, hw_res]
              simp only [Nat.one_ne_zero, ↓reduceIte, hleaf, StateTransitionSpec.clientState,
                Realization.memoryCost_bind', memoryCost_readPackedCompGenProg,
                runClient_state_readPackedCompGenProg, clientResult_readPackedCompGenProg,
                id1, hid1, act, hact, hid_lt, memoryCost_pure]
              omega
            · rw [prog_clientResult_bind, hw_st, hw_res]
              simp only [Nat.one_ne_zero, ↓reduceIte, hleaf, prog_clientResult_bind,
                prog_clientResult_pure, StateTransitionSpec.clientState,
                runClient_state_readPackedCompGenProg, clientResult_readPackedCompGenProg,
                id1, hid1, act, hact, hid_lt, hli_eq, hact_eq]
              simp [extractBufTrie, id1, hid_lt]
    · have hli0 : (extractBufTrie L s.mem).nodeLeafItem leaf = 0 := by
        simp only [extractBufTrie, hleaf, ↓reduceIte]
      refine ⟨?_, ?_, ?_⟩
      · rw [StateTransitionSpec.clientState_bind, hw_st, hw_res]; simp [hleaf]
      · rw [Realization.memoryCost_bind', hw_st, hw_res]
        simp only [Nat.one_ne_zero, ↓reduceIte, hleaf, memoryCost_pure]; omega
      · rw [prog_clientResult_bind, hw_st, hw_res]; simp [hleaf, hli0]

/-- `bufDelete` in `Memory.Prog` (`RealizesBounded .exact`, `¬ReadsWidth`). -/
def bufDeleteBoundedProg : TrieCtx × ℕ → Memory.Prog Unit
  | (ctx, rKey) => do
    let mb ← pure (trieMb ctx)
    let on_ ← pure (trieOn ctx)
    let pb ← pure (triePb ctx)
    let wv ← pure (trieWv ctx)
    let mn ← pure (trieMn ctx)
    let wk ← bufWalkBoundedProg (ctx, rKey)
    if wk.1 = 0 then pure ()
    else if wk.2 < mn then do
      let id1 ← readPackedCompGenProg (((mb, on_), (pb, wv)), 6 * wk.2 + 2)
      let act ← readPackedCompGenProg (((mb, on_), (pb, wv)), 6 * wk.2 + 3)
      if id1 = 0 then pure ()
      else if act = 0 then pure ()
      else writePackedCompGenProg ((((mb, on_), (pb, wv)), 6 * wk.2 + 3), 0)
    else pure ()

theorem realizesBounded_bufDelete :
    RealizesBounded .exact bufDeleteBoundedProg
      (WordEncoding.encode (α := TrieCtx × ℕ))
      (WordEncoding.encode (α := Unit))
      BufLookupPre (fun _ _ => 0) := by
  have hwk := realizesBounded_bufWalkBounded
  have hrp := realizesBounded_readPackedCompGen
  have hwp := realizesBounded_writePackedCompGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨mb, oc⟩, ⟨on_, oi⟩⟩, ⟨⟨pb, wv⟩, ⟨⟨ct, bc⟩, ⟨mn, qm⟩⟩⟩⟩, rKey⟩
    dsimp only [BufLookupPre, TrieLayout.ofCtx] at h
    obtain ⟨hw, hwv, hpb, hbc0, hbc, hbc_pb, hmn1, hmn_pb, hqm_pb, hct_w, hmc, h6m, h6q,
      hd1, hd2, hfr⟩ := h
    subst hwv
    have hvL0 : (TrieLayout.mk mb oc on_ oi pb w ct bc mn qm).Valid w s.frontier :=
      ⟨hw, rfl, hpb, hbc0, hbc, hbc_pb, hmn1, hmn_pb, hqm_pb, hct_w, hmc, h6m, h6q,
        hd1, hd2, hfr⟩
    try dsimp only [Fits, trieMb, trieOn, trieOi, triePb, trieWv, trieCt, trieMn, trieQm] at *
    have hw_st : (Memory.spec 0).clientState s
        (bufWalkBoundedProg ((((mb, oc), (on_, oi)), ((pb, w), ((ct, bc), (mn, qm)))), rKey)) =
        s := by
      unfold bufWalkBoundedProg bufWalkLoopProg
      dsimp only
      have hst_it := (bufWalk_iter_spec hvL0 rKey ct 0 0).2.1
      rw [zero_mul, Nat.shiftRight_zero] at hst_it
      dsimp only [TrieLayout.toCtx] at hst_it
      rw [pure_bind, StateTransitionSpec.clientState_bind, hst_it]
      rfl
    try simp only [StateTransitionSpec.clientState, hw_st,
      runClient_state_readPackedCompGenProg] at *)
  all_goals try exact hvL0
  all_goals try (refine ⟨6 * mn, hw, rfl, hpb, by omega, by omega⟩)
  all_goals omega

theorem bufDeleteBoundedProg_spec {L : TrieLayout} {s : Memory.State}
    (hvL : L.Valid L.w s.frontier) (rKey : ℕ) :
    let s' := (Memory.spec 0).clientState s (bufDeleteBoundedProg (L.toCtx, rKey))
    s'.frontier = s.frontier ∧
    memoryCost (bufDeleteBoundedProg (L.toCtx, rKey)) s ≤ 2 * L.cTab + 8 ∧
    extractBufTrie L s'.mem = bufDelete L.cTab L.bChar (extractBufTrie L s.mem) rKey ∧
    ∀ addr, ¬L.OwnsAddr addr → s'.mem addr = s.mem addr := by
  obtain ⟨_, hst_w, hc_w, hr_w⟩ := bufWalk_iter_spec hvL rKey L.cTab 0 0
  rw [zero_mul, Nat.shiftRight_zero] at hst_w hc_w hr_w
  have hct_proj : L.toCtx.2.2.1.1 = L.cTab := rfl
  have hw_st : (Memory.spec 0).clientState s (bufWalkBoundedProg (L.toCtx, rKey)) = s := by
    unfold bufWalkBoundedProg bufWalkLoopProg; dsimp only
    rw [hct_proj, pure_bind, StateTransitionSpec.clientState_bind, hst_w]; rfl
  have hw_cost : memoryCost (bufWalkBoundedProg (L.toCtx, rKey)) s ≤ 2 * L.cTab := by
    unfold bufWalkBoundedProg bufWalkLoopProg; dsimp only
    rw [hct_proj, pure_bind, Realization.memoryCost_bind', hst_w, memoryCost_pure, add_zero]
    exact hc_w
  have hw_res : (Memory.spec 0).clientResult s (bufWalkBoundedProg (L.toCtx, rKey)) =
      match bufWalk L.bChar (extractBufTrie L s.mem).trieChild rKey L.cTab 0 0 with
      | none => (0, 0)
      | some leaf => (1, leaf) := by
    unfold bufWalkBoundedProg bufWalkLoopProg; dsimp only
    rw [hct_proj, pure_bind, prog_clientResult_bind, hst_w, prog_clientResult_pure]
    exact hr_w
  have hvL_tight : L.Valid L.w (L.metaBase + L.offItem + packedWords (6 * L.qMax + 6) L.ptrB L.w) :=
    ⟨hvL.1, hvL.2.1, hvL.2.2.1, hvL.2.2.2.1, hvL.2.2.2.2.1, hvL.2.2.2.2.2.1,
      hvL.2.2.2.2.2.2.1, hvL.2.2.2.2.2.2.2.1, hvL.2.2.2.2.2.2.2.2.1,
      hvL.2.2.2.2.2.2.2.2.2.1, hvL.2.2.2.2.2.2.2.2.2.2.1, hvL.2.2.2.2.2.2.2.2.2.2.2.1,
      hvL.2.2.2.2.2.2.2.2.2.2.2.2.1, hvL.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      hvL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, le_rfl⟩
  set s_fin := (Memory.spec 0).clientState s (bufDeleteBoundedProg (L.toCtx, rKey))
  have hrun_del : s_fin =
      match bufWalk L.bChar (extractBufTrie L s.mem).trieChild rKey L.cTab 0 0 with
      | none => s
      | some leaf =>
        if leaf < L.maxNodes then
          if readPacked (L.metaBase + L.offNode) L.ptrB L.w s.mem (6 * leaf + 2) = 0 ∨
             readPacked (L.metaBase + L.offNode) L.ptrB L.w s.mem (6 * leaf + 3) = 0 then s
          else { mem := writePacked (L.metaBase + L.offNode) L.ptrB L.w s.mem (6 * leaf + 3) 0,
                 frontier := s.frontier }
        else s := by
    dsimp only [s_fin]
    unfold bufDeleteBoundedProg
    dsimp only [trieMb, trieOn, trieOi, triePb, trieWv, trieCt, trieMn, trieQm]
    simp only [pure_bind]
    have hp1 : L.toCtx.1.1.1 = L.metaBase := rfl
    have hp2 : L.toCtx.1.2.1 = L.offNode := rfl
    have hp4 : L.toCtx.2.1.1 = L.ptrB := rfl
    have hp5 : L.toCtx.2.1.2 = L.w := rfl
    have hp6 : L.toCtx.2.2.2.1 = L.maxNodes := rfl
    rw [hp1, hp2, hp4, hp5, hp6, StateTransitionSpec.clientState_bind, hw_st, hw_res]
    cases bufWalk L.bChar (extractBufTrie L s.mem).trieChild rKey L.cTab 0 0 with
    | none => rfl
    | some leaf =>
      dsimp only
      by_cases hl : leaf < L.maxNodes
      · by_cases h0 : readPacked (L.metaBase + L.offNode) L.ptrB L.w s.mem (6 * leaf + 2) = 0
        · simp [hl, h0]
        · by_cases h1 : readPacked (L.metaBase + L.offNode) L.ptrB L.w s.mem (6 * leaf + 3) = 0
          · simp [hl, h0, h1]
          · simp [hl, h0, h1]
      · simp [hl]
  have hcost_del : memoryCost (bufDeleteBoundedProg (L.toCtx, rKey)) s ≤ 2 * L.cTab + 8 := by
    unfold bufDeleteBoundedProg
    dsimp only [trieMb, trieOn, trieOi, triePb, trieWv, trieCt, trieMn, trieQm]
    simp only [pure_bind]
    have hp1 : L.toCtx.1.1.1 = L.metaBase := rfl
    have hp2 : L.toCtx.1.2.1 = L.offNode := rfl
    have hp4 : L.toCtx.2.1.1 = L.ptrB := rfl
    have hp5 : L.toCtx.2.1.2 = L.w := rfl
    have hp6 : L.toCtx.2.2.2.1 = L.maxNodes := rfl
    rw [hp1, hp2, hp4, hp5, hp6, Realization.memoryCost_bind', hw_st, hw_res]
    cases bufWalk L.bChar (extractBufTrie L s.mem).trieChild rKey L.cTab 0 0 with
    | none => simp only [↓reduceIte, memoryCost_pure]; omega
    | some leaf =>
      dsimp only
      by_cases hl : leaf < L.maxNodes
      · simp only [Nat.one_ne_zero, ↓reduceIte, hl, Realization.memoryCost_bind',
          memoryCost_readPackedCompGenProg, StateTransitionSpec.clientState,
          runClient_state_readPackedCompGenProg, clientResult_readPackedCompGenProg]
        split_ifs <;> simp only [memoryCost_pure, memoryCost_writePackedCompGenProg] <;> omega
      · simp only [Nat.one_ne_zero, ↓reduceIte, hl, memoryCost_pure]; omega
  change s_fin.frontier = s.frontier ∧ _ ∧ extractBufTrie L s_fin.mem = _ ∧ _
  rw [hrun_del]
  unfold bufDelete
  cases hwalk : bufWalk L.bChar (extractBufTrie L s.mem).trieChild rKey L.cTab 0 0 with
  | none => exact ⟨rfl, hcost_del, rfl, fun _ _ => rfl⟩
  | some leaf =>
    dsimp only
    by_cases hleaf : leaf < L.maxNodes
    · simp only [hleaf, ↓reduceIte]
      have hli : (extractBufTrie L s.mem).nodeLeafItem leaf =
          readPacked (L.metaBase + L.offNode) L.ptrB L.w s.mem (6 * leaf + 2) := by
        simp only [extractBufTrie, hleaf, ↓reduceIte]
      have hact : (extractBufTrie L s.mem).nodeActive leaf =
          readPacked (L.metaBase + L.offNode) L.ptrB L.w s.mem (6 * leaf + 3) := by
        simp only [extractBufTrie, hleaf, ↓reduceIte]
      rw [hli, hact]
      split_ifs with hcond
      · exact ⟨rfl, hcost_del, rfl, fun _ _ => rfl⟩
      · obtain ⟨hext_u, hfr_u⟩ := extractBufTrie_writeNodeField (mem := s.mem)
          (u := leaf) (fld := 3) (val := 0) hvL_tight hleaf (by decide) (Nat.two_pow_pos _)
        exact ⟨rfl, hcost_del, hext_u, hfr_u⟩
    · simp only [hleaf, ↓reduceIte]
      have hli0 : (extractBufTrie L s.mem).nodeLeafItem leaf = 0 := by
        simp only [extractBufTrie, hleaf, ↓reduceIte]
      simp only [hli0, true_or, ↓reduceIte]
      exact ⟨trivial, hcost_del, trivial, fun _ _ => trivial⟩

/-- Allocate a new trie child `u` along `(cur, ch)` inside `bufEnsurePath`. -/
private def bufAllocNodeProg : TrieCtx × (ℕ × ℕ) → Memory.Prog ℕ
  | ((((mb, oc), (on_, oi)), ((pb, wv), ((_ct, bc), (mn, qm)))), (cur, ch)) => do
    let u ← readPackedCompGenProg (((mb, oi), (pb, wv)), 6 * qm)
    if cur < mn then
      if u < mn then do
        writePackedCompGenProg ((((mb, oc), (pb, wv)), (cur <<< bc) + ch), u)
        writePackedCompGenProg ((((mb, on_), (pb, wv)), 6 * u), cur)
        writePackedCompGenProg ((((mb, on_), (pb, wv)), 6 * u + 1), ch)
        writePackedCompGenProg ((((mb, on_), (pb, wv)), 6 * u + 2), 0)
        writePackedCompGenProg ((((mb, oi), (pb, wv)), 6 * qm), u + 1)
        pure u
      else pure 0
    else pure 0

private def BufAllocNodePre (w : ℕ) : TrieCtx × (ℕ × ℕ) → Memory.State → Prop
  | (ctx, (_cur, ch)), s =>
    let L := TrieLayout.ofCtx ctx
    L.Valid w s.frontier ∧ ch < 2 ^ L.bChar

private theorem realizesBounded_bufAllocNode :
    RealizesBounded .exact bufAllocNodeProg
      (WordEncoding.encode (α := TrieCtx × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      BufAllocNodePre (fun _ _ => 0) := by
  have hrp := realizesBounded_readPackedCompGen
  have hwp := realizesBounded_writePackedCompGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨mb, oc⟩, ⟨on_, oi⟩⟩, ⟨⟨pb, wv⟩, ⟨⟨ct, bc⟩, ⟨mn, qm⟩⟩⟩⟩, ⟨cur, ch⟩⟩
    dsimp only [BufAllocNodePre, TrieLayout.ofCtx] at h
    obtain ⟨hvL, hch⟩ := h
    obtain ⟨hw, hwv, hpb, _, hbc, _, hmn1, hmn_pb, _, _, hmc, h6m, h6q, hd1, hd2, hfr⟩ := hvL
    subst hwv
    try dsimp only [Fits] at *
    try simp only [StateTransitionSpec.clientState, runClient_state_readPackedCompGenProg,
      runClient_state_writePackedCompGenProg, clientResult_readPackedCompGenProg] at *
    have hmn_w : mn < 2 ^ w := hmn_pb.trans_le (Nat.pow_le_pow_right (by decide) hpb)
    have hpow_bc_w : 2 ^ bc < 2 ^ w := Nat.pow_lt_pow_right Nat.one_lt_two hbc
    have hbc_w : bc < 2 ^ w := hbc.trans Nat.lt_two_pow_self
    have hch_w : ch < 2 ^ w := hch.trans hpow_bc_w
    have h1_lt : 1 < 2 ^ w := Nat.one_lt_two_pow hw.ne'
    have h6_lt : 6 < 2 ^ w := (Nat.le_mul_of_pos_right 6 hmn1).trans_lt h6m)
  all_goals try omega
  all_goals try exact ⟨6 * qm + 6, hw, rfl, hpb, by omega,
    show mb + oi + packedWords (6 * qm + 6) pb w ≤ s.frontier by omega⟩
  all_goals try exact ⟨6 * mn, hw, rfl, hpb, by omega,
    show mb + on_ + packedWords (6 * mn) pb w ≤ s.frontier by omega⟩
  all_goals (
    have hsh := child_idx_lt ‹cur < mn› hch
    try omega
    try exact ⟨mn * 2 ^ bc, hw, rfl, hpb, hsh,
      show mb + oc + packedWords (mn * 2 ^ bc) pb w ≤ s.frontier by omega⟩)

/-- Single step of `bufEnsurePath` in `Memory.Prog` (`1 ≤ memoryCost` unconditionally). -/
private def bufEnsureStepProg : TrieCtx × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ)
  | (ctx, (cur, remKey)) => do
    let mb ← pure ctx.1.1.1
    let oc ← pure ctx.1.1.2
    let pb ← pure ctx.2.1.1
    let wv ← pure ctx.2.1.2
    let bc ← pure ctx.2.2.1.2
    let mn ← pure ctx.2.2.2.1
    let ch ← pure (remKey &&& ((1 <<< bc) - 1))
    let idx ← if cur < mn then pure ((cur <<< bc) + ch) else pure 0
    let nxt ← readPackedCompGenProg (((mb, oc), (pb, wv)), idx)
    if cur < mn then
      if nxt = 0 then do
        let u ← bufAllocNodeProg (ctx, (cur, ch))
        pure (u, remKey >>> bc)
      else
        pure (nxt, remKey >>> bc)
    else pure (0, remKey >>> bc)

private theorem memoryCost_bufEnsureStepProg_pos (x : TrieCtx × (ℕ × ℕ)) (s : Memory.State) :
    1 ≤ memoryCost (bufEnsureStepProg x) s := by
  rcases x with ⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩⟩, ⟨_, _⟩⟩
  unfold bufEnsureStepProg
  simp only [pure_bind]
  split_ifs <;>
    simp only [Realization.memoryCost_bind', memoryCost_readPackedCompGenProg,
      runClient_state_readPackedCompGenProg, memoryCost_pure] <;>
    omega

private def BufEnsureStepPre (w : ℕ) : TrieCtx × (ℕ × ℕ) → Memory.State → Prop
  | (ctx, _st), s => (TrieLayout.ofCtx ctx).Valid w s.frontier

private theorem realizesBounded_bufEnsureStep :
    RealizesBounded .exact bufEnsureStepProg
      (WordEncoding.encode (α := TrieCtx × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      BufEnsureStepPre (fun _ _ => 0) := by
  have hrp := realizesBounded_readPackedCompGen
  have hal := realizesBounded_bufAllocNode
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨mb, oc⟩, ⟨on_, oi⟩⟩, ⟨⟨pb, wv⟩, ⟨⟨ct, bc⟩, ⟨mn, qm⟩⟩⟩⟩, ⟨cur, rk⟩⟩
    dsimp only [BufEnsureStepPre, TrieLayout.ofCtx] at h
    obtain ⟨hw, hwv, hpb, hbc0, hbc, hbc_pb, hmn1, hmn_pb, hqm_pb, hct_w, hmc, h6m, h6q,
      hd1, hd2, hfr⟩ := h
    subst hwv
    have hvL0 : (TrieLayout.mk mb oc on_ oi pb w ct bc mn qm).Valid w s.frontier :=
      ⟨hw, rfl, hpb, hbc0, hbc, hbc_pb, hmn1, hmn_pb, hqm_pb, hct_w, hmc, h6m, h6q,
        hd1, hd2, hfr⟩
    try dsimp only [Fits, trieMb, trieOn, trieOi, triePb, trieWv, trieCt, trieMn, trieQm] at *
    have hpow_bc : 2 ^ bc < 2 ^ w := Nat.pow_lt_pow_right Nat.one_lt_two hbc
    have hch_lt : rk &&& (2 ^ bc - 1) < 2 ^ bc := by
      rw [Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_lt _ (Nat.two_pow_pos bc)
    try simp only [Nat.shiftLeft_eq 1, one_mul, StateTransitionSpec.clientState,
      runClient_state_readPackedCompGenProg] at *)
  all_goals try exact Nat.one_le_two_pow
  all_goals try exact hpow_bc
  all_goals try exact ⟨hvL0, hch_lt⟩
  all_goals try exact ⟨mn * 2 ^ bc, hw, rfl, hpb, Nat.mul_pos hmn1 (Nat.two_pow_pos bc), by omega⟩
  all_goals (
    have hsh := child_idx_lt ‹cur < mn› hch_lt
    try exact hsh.trans hmc
    try exact ⟨mn * 2 ^ bc, hw, rfl, hpb, hsh, by omega⟩)

private def bufEnsureLoopProg : (TrieCtx × (ℕ × ℕ)) × ℕ → Memory.Prog (ℕ × ℕ)
  | ((ctx, st), fuel) => iterate bufEnsureStepProg ctx fuel st

private theorem realizesBounded_bufEnsureLoop :
    RealizesBounded .exact bufEnsureLoopProg
      (WordEncoding.encode (α := (TrieCtx × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w ((ctx, st), fuel) s =>
        iterationSafe bufEnsureStepProg BufEnsureStepPre w ctx fuel st s)
      (fun _ _ => 0) :=
  RealizesBounded.iterate₀
    (WordEncoding.encode (α := TrieCtx))
    (WordEncoding.encode (α := ℕ × ℕ))
    realizesBounded_bufEnsureStep
    memoryCost_bufEnsureStepProg_pos

/-- Leaf-slot attachment tail of `bufInsert` in `Memory.Prog`. -/
private def bufAttachLeafProg : TrieCtx × (ℕ × (ℕ × ℕ)) → Memory.Prog Unit
  | ((((mb, _oc), (on_, oi)), ((pb, wv), ((_ct, _bc), (mn, qm)))), (leaf, (bkt, loc))) =>
    if leaf < mn then do
      let id1 ← readPackedCompGenProg (((mb, on_), (pb, wv)), 6 * leaf + 2)
      if id1 = 0 then do
        let id ← readPackedCompGenProg (((mb, oi), (pb, wv)), 6 * qm + 1)
        if id < qm then do
          writePackedCompGenProg ((((mb, oi), (pb, wv)), 6 * qm + 1), id + 1)
          writePackedCompGenProg ((((mb, on_), (pb, wv)), 6 * leaf + 2), id + 1)
          writePackedCompGenProg ((((mb, on_), (pb, wv)), 6 * leaf + 3), 1)
          writePackedCompGenProg ((((mb, oi), (pb, wv)), 6 * id), leaf)
          writePackedCompGenProg ((((mb, oi), (pb, wv)), 6 * id + 1), bkt)
          writePackedCompGenProg ((((mb, oi), (pb, wv)), 6 * id + 2), loc)
        else pure ()
      else do
        let id ← pure (id1 - 1)
        if id < qm then do
          writePackedCompGenProg ((((mb, on_), (pb, wv)), 6 * leaf + 3), 1)
          writePackedCompGenProg ((((mb, oi), (pb, wv)), 6 * id + 1), bkt)
          writePackedCompGenProg ((((mb, oi), (pb, wv)), 6 * id + 2), loc)
        else pure ()
    else pure ()

private def BufAttachLeafPre (w : ℕ) : TrieCtx × (ℕ × (ℕ × ℕ)) → Memory.State → Prop
  | (ctx, _args), s => (TrieLayout.ofCtx ctx).Valid w s.frontier

private theorem realizesBounded_bufAttachLeaf :
    RealizesBounded .exact bufAttachLeafProg
      (WordEncoding.encode (α := TrieCtx × (ℕ × (ℕ × ℕ))))
      (WordEncoding.encode (α := Unit))
      BufAttachLeafPre (fun _ _ => 0) := by
  have hrp := realizesBounded_readPackedCompGen
  have hwp := realizesBounded_writePackedCompGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨mb, oc⟩, ⟨on_, oi⟩⟩, ⟨⟨pb, wv⟩, ⟨⟨ct, bc⟩, ⟨mn, qm⟩⟩⟩⟩, ⟨leaf, ⟨bkt, loc⟩⟩⟩
    dsimp only [BufAttachLeafPre, TrieLayout.ofCtx] at h
    obtain ⟨hw, hwv, hpb, _, _, _, hmn1, _, hqm_pb, _, _, h6m, h6q, hd1, hd2, hfr⟩ := h
    subst hwv
    try dsimp only [Fits] at *
    try simp only [StateTransitionSpec.clientState, runClient_state_readPackedCompGenProg,
      runClient_state_writePackedCompGenProg, clientResult_readPackedCompGenProg] at *
    have h1_lt : 1 < 2 ^ w := Nat.one_lt_two_pow hw.ne'
    have h6_lt : 6 < 2 ^ w := (Nat.le_mul_of_pos_right 6 hmn1).trans_lt h6m
    have hqm_w : qm < 2 ^ w := hqm_pb.trans_le (Nat.pow_le_pow_right (by decide) hpb)
    have hid1_w : readPacked (mb + on_) pb w s.mem (6 * leaf + 2) < 2 ^ w :=
      (readPacked_lt _ _ _ _ _).trans_le (Nat.pow_le_pow_right (by decide) hpb))
  all_goals try omega
  all_goals try exact ⟨6 * mn, hw, rfl, hpb, by omega,
    show mb + on_ + packedWords (6 * mn) pb w ≤ s.frontier by omega⟩
  all_goals exact ⟨6 * qm + 6, hw, rfl, hpb, by omega,
    show mb + oi + packedWords (6 * qm + 6) pb w ≤ s.frontier by omega⟩

/-- `bufInsert` in `Memory.Prog` (`RealizesBounded .exact`, `¬ReadsWidth`). -/
def bufInsertBoundedProg : TrieCtx × (ℕ × (ℕ × ℕ)) → Memory.Prog Unit
  | (ctx, (rKey, (bkt, loc))) => do
    let cTab ← pure (trieCt ctx)
    let p ← bufEnsureLoopProg ((ctx, (0, rKey)), cTab)
    bufAttachLeafProg (ctx, (p.1, (bkt, loc)))

/-- Precondition for `bufInsertBoundedProg`. -/
@[expose] def BufInsertPre (w : ℕ) : TrieCtx × (ℕ × (ℕ × ℕ)) → Memory.State → Prop
  | (ctx, _args), s => (TrieLayout.ofCtx ctx).Valid w s.frontier

private theorem bufEnsure_iter_safe {L : TrieLayout} :
    ∀ m (st : ℕ × ℕ) (s : Memory.State),
      L.Valid L.w s.frontier →
      iterationSafe bufEnsureStepProg BufEnsureStepPre L.w L.toCtx m st s ∧
      ((Memory.spec 0).clientState s (iterate bufEnsureStepProg L.toCtx m st)).frontier =
        s.frontier ∧
      memoryCost (iterate bufEnsureStepProg L.toCtx m st) s ≤ 24 * m ∧
      ∀ addr, ¬L.OwnsAddr addr →
        ((Memory.spec 0).clientState s (iterate bufEnsureStepProg L.toCtx m st)).mem addr =
          s.mem addr := by
  intro m
  induction m with
  | zero => intro st s _; exact ⟨trivial, rfl, Nat.zero_le _, fun _ _ => rfl⟩
  | succ m ih =>
    intro ⟨cur, rk⟩ s hvL
    have hvL0 := hvL
    obtain ⟨hw, _, _, _, _, _, _, _, _, _, _, _, _, hd1, hd2, _⟩ := hvL0
    set s₁ := (Memory.spec 0).clientState s (bufEnsureStepProg (L.toCtx, (cur, rk)))
    set res₁ := (Memory.spec 0).clientResult s (bufEnsureStepProg (L.toCtx, (cur, rk)))
    have hch_lt : rk &&& ((1 <<< L.bChar) - 1) < 2 ^ L.bChar := by
      rw [Nat.shiftLeft_eq, one_mul, Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
    have hs1_props : s₁.frontier = s.frontier ∧
        memoryCost (bufEnsureStepProg (L.toCtx, (cur, rk))) s ≤ 24 ∧
        ∀ addr, ¬L.OwnsAddr addr → s₁.mem addr = s.mem addr := by
      dsimp only [s₁]
      unfold bufEnsureStepProg bufAllocNodeProg
      dsimp only [TrieLayout.toCtx]
      simp only [pure_bind]
      by_cases hcur : cur < L.maxNodes
      · simp only [hcur, ↓reduceIte]
        rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
          clientState_readPackedCompGenProg, memoryCost_readPackedCompGenProg,
          clientResult_readPackedCompGenProg]
        by_cases hnxt0 : readPacked (L.metaBase + L.offChild) L.ptrB L.w s.mem
            ((cur <<< L.bChar) + (rk &&& ((1 <<< L.bChar) - 1))) = 0
        · simp only [hnxt0, ↓reduceIte]
          rw [bind_assoc, StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
            clientState_readPackedCompGenProg, memoryCost_readPackedCompGenProg,
            clientResult_readPackedCompGenProg]
          by_cases hu_lt : readPacked (L.metaBase + L.offItem) L.ptrB L.w s.mem (6 * L.qMax) <
              L.maxNodes
          · simp only [hu_lt, ↓reduceIte, bind_assoc, pure_bind,
              StateTransitionSpec.clientState, prog_runClient_state_bind,
              runClient_state_writePackedCompGenProg, prog_runClient_state_pure,
              Realization.memoryCost_bind', memoryCost_writePackedCompGenProg, memoryCost_pure]
            refine ⟨trivial, by omega, fun addr ha => ?_⟩
            rw [writePacked_outside hw _ (by omega : 6 * L.qMax < 6 * L.qMax + 6) _
              (fun h => ha (Or.inr (Or.inr h)))]
            rw [writePacked_outside hw _ (by omega : 6 * _ + 2 < 6 * L.maxNodes) _
              (fun h => ha (Or.inr (Or.inl h)))]
            rw [writePacked_outside hw _ (by omega : 6 * _ + 1 < 6 * L.maxNodes) _
              (fun h => ha (Or.inr (Or.inl h)))]
            rw [writePacked_outside hw _ (by omega : 6 * _ < 6 * L.maxNodes) _
              (fun h => ha (Or.inr (Or.inl h)))]
            exact writePacked_outside hw _ (child_idx_lt hcur hch_lt) _ (fun h => ha (Or.inl h))
          · simp only [hu_lt, ↓reduceIte, pure_bind,
              StateTransitionSpec.clientState, prog_runClient_state_pure, memoryCost_pure]
            exact ⟨trivial, by omega, fun _ _ => trivial⟩
        · simp only [hnxt0, ↓reduceIte, StateTransitionSpec.clientState,
            prog_runClient_state_pure, memoryCost_pure]
          exact ⟨trivial, by omega, fun _ _ => trivial⟩
      · simp only [hcur, ↓reduceIte]
        rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
          clientState_readPackedCompGenProg, memoryCost_readPackedCompGenProg]
        simp only [StateTransitionSpec.clientState,
          prog_runClient_state_pure, memoryCost_pure]
        exact ⟨trivial, by omega, fun _ _ => trivial⟩
    have hvL₁ : L.Valid L.w s₁.frontier := by rwa [hs1_props.1]
    obtain ⟨hs_m, hfr_m, hc_m, hout_m⟩ := ih res₁ s₁ hvL₁
    refine ⟨⟨by simpa only [BufEnsureStepPre, TrieLayout.ofCtx_toCtx] using hvL, hs_m⟩, ?_, ?_, ?_⟩
    · unfold iterate; rw [StateTransitionSpec.clientState_bind]; exact hfr_m.trans hs1_props.1
    · unfold iterate; rw [Realization.memoryCost_bind']
      have hc1 := hs1_props.2.1
      change _ + memoryCost (iterate bufEnsureStepProg L.toCtx m res₁) s₁ ≤ _
      omega
    · intro addr ha
      unfold iterate; rw [StateTransitionSpec.clientState_bind]
      exact (hout_m addr ha).trans (hs1_props.2.2 addr ha)

theorem realizesBounded_bufInsert :
    RealizesBounded .exact bufInsertBoundedProg
      (WordEncoding.encode (α := TrieCtx × (ℕ × (ℕ × ℕ))))
      (WordEncoding.encode (α := Unit))
      BufInsertPre (fun _ _ => 0) := by
  have hloop := realizesBounded_bufEnsureLoop
  have hatt := realizesBounded_bufAttachLeaf
  realize
  all_goals (
    rcases d with ⟨ctx, ⟨rKey, ⟨bkt, loc⟩⟩⟩
    have hvL : (TrieLayout.ofCtx ctx).Valid w s.frontier := h
    have hw_eq : (TrieLayout.ofCtx ctx).w = w := hvL.2.1.symm
    have hto : (TrieLayout.ofCtx ctx).toCtx = ctx := by
      rcases ctx with ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩⟩; rfl
    have hct_eq : ctx.2.2.1.1 = (TrieLayout.ofCtx ctx).cTab := by
      rcases ctx with ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩⟩; rfl
    obtain ⟨hsafe, hfr_eq, _, _⟩ := bufEnsure_iter_safe (L := TrieLayout.ofCtx ctx)
      (TrieLayout.ofCtx ctx).cTab (0, rKey) s (by rwa [hw_eq]))
  all_goals try (rw [hw_eq, hto, ← hct_eq] at hsafe; exact hsafe)
  all_goals (
    unfold BufAttachLeafPre bufEnsureLoopProg
    rw [StateTransitionSpec.clientState] at hfr_eq ⊢
    rw [hto, ← hct_eq] at hfr_eq
    simpa only [prog_clientResult_pure, prog_runClient_state_pure, hfr_eq] using hvL)

private theorem bufEnsure_iter_spec {L : TrieLayout} (hvL : L.Valid L.w (L.metaBase + L.offItem +
    packedWords (6 * L.qMax + 6) L.ptrB L.w)) (rKey : ℕ) :
    ∀ m off (cur : ℕ) (s : Memory.State),
      cur < (extractBufTrie L s.mem).nodeAlloc →
      (extractBufTrie L s.mem).nodeAlloc + m ≤ L.maxNodes →
      (∀ v ch, (extractBufTrie L s.mem).trieChild v ch ≠ 0 →
        (extractBufTrie L s.mem).trieChild v ch < (extractBufTrie L s.mem).nodeAlloc) →
      let p_pure := bufEnsurePath L.bChar rKey m off (extractBufTrie L s.mem) cur
      let s' := (Memory.spec 0).clientState s
        (iterate bufEnsureStepProg L.toCtx m (cur, rKey >>> (off * L.bChar)))
      let r' := (Memory.spec 0).clientResult s
        (iterate bufEnsureStepProg L.toCtx m (cur, rKey >>> (off * L.bChar)))
      extractBufTrie L s'.mem = p_pure.1 ∧ r'.1 = p_pure.2 ∧
      p_pure.2 < p_pure.1.nodeAlloc ∧ p_pure.1.nodeAlloc ≤ L.maxNodes := by
  intro m
  induction m with
  | zero =>
    intro off cur s hcur hna _
    exact ⟨rfl, rfl, hcur, hna⟩
  | succ m ih =>
    intro off cur s hcur hna hchild_lt
    set tr := extractBufTrie L s.mem
    set rk := rKey >>> (off * L.bChar)
    set ch := laneGet L.bChar rKey off
    have hch_eq : rk &&& ((1 <<< L.bChar) - 1) = ch := by rw [Nat.shiftLeft_eq, one_mul]; rfl
    have hch_lt : ch < 2 ^ L.bChar := laneGet_lt _ _ _
    have hrk_next : rk >>> L.bChar = rKey >>> ((off + 1) * L.bChar) := by
      dsimp only [rk]; rw [← Nat.shiftRight_add, ← Nat.add_one_mul]
    have hcur_mn : cur < L.maxNodes := by omega
    have hu_mn : tr.nodeAlloc < L.maxNodes := by omega
    set nxt := readPacked (L.metaBase + L.offChild) L.ptrB L.w s.mem ((cur <<< L.bChar) + ch)
    have htr_ch : tr.trieChild cur ch = nxt := by
      simp only [tr, extractBufTrie, hcur_mn, hch_lt, and_self, ↓reduceIte, nxt]
    by_cases hnxt0 : nxt = 0
    · set u := tr.nodeAlloc
      have hu_pb : u < 2 ^ L.ptrB := hu_mn.trans hvL.2.2.2.2.2.2.2.1
      have hu1_pb : u + 1 < 2 ^ L.ptrB :=
        (by omega : u + 1 ≤ L.maxNodes).trans_lt hvL.2.2.2.2.2.2.2.1
      have hcur_pb : cur < 2 ^ L.ptrB := hcur.trans hu_pb
      have hch_pb : ch < 2 ^ L.ptrB := hch_lt.trans_le hvL.2.2.2.2.2.1
      set m1 := writePacked (L.metaBase + L.offChild) L.ptrB L.w s.mem ((cur <<< L.bChar) + ch) u
      set m2 := writePacked (L.metaBase + L.offNode) L.ptrB L.w m1 (6 * u) cur
      set m3 := writePacked (L.metaBase + L.offNode) L.ptrB L.w m2 (6 * u + 1) ch
      set m4 := writePacked (L.metaBase + L.offNode) L.ptrB L.w m3 (6 * u + 2) 0
      set m5 := writePacked (L.metaBase + L.offItem) L.ptrB L.w m4 (6 * L.qMax) (u + 1)
      have he1 := (extractBufTrie_writeChild hvL hcur_mn hch_lt hu_pb (mem := s.mem)).1
      have he2 := (extractBufTrie_writeNodeField (fld := 0) hvL hu_mn (by decide) hcur_pb
        (mem := m1)).1
      have he3 := (extractBufTrie_writeNodeField (fld := 1) hvL hu_mn (by decide) hch_pb
        (mem := m2)).1
      have he4 := (extractBufTrie_writeNodeField (fld := 2) hvL hu_mn (by decide)
        (Nat.two_pow_pos _) (mem := m3)).1
      have he5 := (extractBufTrie_writeHeader (isItem := 0) hvL (by decide) hu1_pb (mem := m4)).1
      simp only [Nat.add_zero] at he2 he5
      simp only [↓reduceIte] at he5
      set tr1 : BufTrie :=
        { tr with
          nodeAlloc := u + 1
          trieChild := Function.update tr.trieChild cur (Function.update (tr.trieChild cur) ch u)
          nodeParent := Function.update tr.nodeParent u cur
          nodeChar := Function.update tr.nodeChar u ch
          nodeLeafItem := Function.update tr.nodeLeafItem u 0 }
      have hm5_eq : extractBufTrie L m5 = tr1 := by
        dsimp only [m5, m4, m3, m2, m1] at he5 he4 he3 he2 he1 ⊢
        rw [he5, he4, he3, he2, he1]
        rfl
      have hstep_run : (Memory.spec 0).clientState s (bufEnsureStepProg (L.toCtx, (cur, rk))) =
          ⟨m5, s.frontier⟩ ∧
          (Memory.spec 0).clientResult s (bufEnsureStepProg (L.toCtx, (cur, rk))) =
          (u, rKey >>> ((off + 1) * L.bChar)) := by
        unfold bufEnsureStepProg bufAllocNodeProg
        dsimp only [TrieLayout.toCtx]
        have hu_def : readPacked (L.metaBase + L.offItem) L.ptrB L.w s.mem (6 * L.qMax) = u := rfl
        simp [hcur_mn, hch_eq, nxt, hnxt0, hu_def, hu_mn, hrk_next, m1, m2, m3, m4, m5]
      have hchild_lt1 : ∀ v c, tr1.trieChild v c ≠ 0 → tr1.trieChild v c < tr1.nodeAlloc := by
        intro v c hnz
        dsimp only [tr1] at hnz ⊢
        by_cases hv_eq : v = cur
        · subst hv_eq
          by_cases hc_eq : c = ch
          · subst hc_eq; simp
          · simp only [Function.update_self, Function.update_of_ne hc_eq] at hnz ⊢
            exact (hchild_lt v c hnz).trans (Nat.lt_succ_self u)
        · simp only [Function.update_of_ne hv_eq] at hnz ⊢
          exact (hchild_lt v c hnz).trans (Nat.lt_succ_self u)
      obtain ⟨hext_rec, hr_rec, hleaf_lt, hna_le⟩ := ih (off + 1) u ⟨m5, s.frontier⟩
        (by rw [hm5_eq]; dsimp only [tr1]; omega)
        (by rw [hm5_eq]; dsimp only [tr1]; omega)
        (by rw [hm5_eq]; exact hchild_lt1)
      have hpure_eq : bufEnsurePath L.bChar rKey (m + 1) off tr cur =
          bufEnsurePath L.bChar rKey m (off + 1) tr1 u := by
        dsimp only [bufEnsurePath]
        simp only [ch, htr_ch, hnxt0, ↓reduceIte]
        rfl
      unfold iterate
      rw [StateTransitionSpec.clientState_bind, prog_clientResult_bind, hstep_run.1, hstep_run.2,
        hpure_eq]
      rw [hm5_eq] at hext_rec hr_rec hleaf_lt hna_le
      exact ⟨hext_rec, hr_rec, hleaf_lt, hna_le⟩
    · have hnxt_lt : nxt < tr.nodeAlloc := htr_ch ▸ hchild_lt cur ch (htr_ch.symm ▸ hnxt0)
      have hstep_run : (Memory.spec 0).clientState s (bufEnsureStepProg (L.toCtx, (cur, rk))) = s ∧
          (Memory.spec 0).clientResult s (bufEnsureStepProg (L.toCtx, (cur, rk))) =
          (nxt, rKey >>> ((off + 1) * L.bChar)) := by
        unfold bufEnsureStepProg
        dsimp only [TrieLayout.toCtx]
        simp [hcur_mn, hch_eq, nxt, hnxt0, hrk_next]
      obtain ⟨hext_rec, hr_rec, hleaf_lt, hna_le⟩ :=
        ih (off + 1) nxt s hnxt_lt (by dsimp only [tr] at hna; omega) hchild_lt
      have hpure_eq : bufEnsurePath L.bChar rKey (m + 1) off tr cur =
          bufEnsurePath L.bChar rKey m (off + 1) tr nxt := by
        dsimp only [bufEnsurePath]; simp [ch, htr_ch, hnxt0]
      unfold iterate
      rw [StateTransitionSpec.clientState_bind, prog_clientResult_bind, hstep_run.1, hstep_run.2,
        hpure_eq]
      exact ⟨hext_rec, hr_rec, hleaf_lt, hna_le⟩

/-- When `bufWalk` already reaches `some leaf`, `bufEnsurePath` leaves the trie unchanged and
returns `(tr, leaf)`. -/
theorem bufEnsurePath_eq_of_walk_some {bChar rKey : ℕ} :
    ∀ m off (tr : BufTrie) (cur leaf : ℕ),
      bufWalk bChar tr.trieChild rKey m off cur = some leaf →
      bufEnsurePath bChar rKey m off tr cur = (tr, leaf) := by
  intro m
  induction m with
  | zero =>
    intro _ tr cur leaf hw
    dsimp only [bufWalk] at hw
    cases hw; rfl
  | succ m ih =>
    intro off tr cur leaf hw
    dsimp only [bufWalk] at hw
    dsimp only [bufEnsurePath]
    by_cases h0 : tr.trieChild cur (laneGet bChar rKey off) = 0
    · rw [ite_eq_left h0] at hw; cases hw
    · rw [ite_eq_right h0] at hw
      rw [ite_eq_right h0]
      exact ih (off + 1) tr _ leaf hw

private theorem bufInsertBoundedProg_spec_core {L : TrieLayout} {s : Memory.State}
    (hvL : L.Valid L.w s.frontier)
    {mapFn : ℕ → Option (ℕ × ℕ)}
    (hv : ValidBufTrie L.cTab L.bChar (extractBufTrie L s.mem) mapFn)
    (hraw : RawBufTrieBounds (extractBufTrie L s.mem))
    (hna : (extractBufTrie L s.mem).nodeAlloc + L.cTab ≤ L.maxNodes)
    {rKey bkt loc : ℕ}
    (hia_or : (extractBufTrie L s.mem).itemAlloc < L.qMax ∨
      ((extractBufTrie L s.mem).itemAlloc ≤ L.qMax ∧ mapFn rKey ≠ none))
    (hk : rKey < 2 ^ (L.cTab * L.bChar))
    (hbkt : bkt < 2 ^ L.ptrB) (hloc : loc < 2 ^ L.ptrB) :
    let s' := (Memory.spec 0).clientState s (bufInsertBoundedProg (L.toCtx, (rKey, (bkt, loc))))
    s'.frontier = s.frontier ∧
    memoryCost (bufInsertBoundedProg (L.toCtx, (rKey, (bkt, loc)))) s ≤ 24 * L.cTab + 32 ∧
    extractBufTrie L s'.mem = bufInsert L.cTab L.bChar (extractBufTrie L s.mem) rKey bkt loc ∧
    ValidBufTrie L.cTab L.bChar (extractBufTrie L s'.mem)
      (Function.update mapFn rKey (some (bkt, loc))) ∧
    ∀ addr, ¬L.OwnsAddr addr → s'.mem addr = s.mem addr := by
  have hvL_tight : L.Valid L.w (L.metaBase + L.offItem + packedWords (6 * L.qMax + 6) L.ptrB L.w) :=
    ⟨hvL.1, hvL.2.1, hvL.2.2.1, hvL.2.2.2.1, hvL.2.2.2.2.1, hvL.2.2.2.2.2.1,
      hvL.2.2.2.2.2.2.1, hvL.2.2.2.2.2.2.2.1, hvL.2.2.2.2.2.2.2.2.1,
      hvL.2.2.2.2.2.2.2.2.2.1, hvL.2.2.2.2.2.2.2.2.2.2.1, hvL.2.2.2.2.2.2.2.2.2.2.2.1,
      hvL.2.2.2.2.2.2.2.2.2.2.2.2.1, hvL.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      hvL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, le_rfl⟩
  obtain ⟨h1_na, hchild_lt, hleaf_inv⟩ := hraw
  obtain ⟨_, hfr1, hc1, hout1⟩ := bufEnsure_iter_safe L.cTab (0, rKey) s hvL
  obtain ⟨hext1, hr1, hleaf_lt1, hna_le1⟩ := bufEnsure_iter_spec hvL_tight rKey L.cTab 0 0 s
    (by omega) hna hchild_lt
  rw [zero_mul, Nat.shiftRight_zero] at hext1 hr1
  set s₁ := (Memory.spec 0).clientState s (iterate bufEnsureStepProg L.toCtx L.cTab (0, rKey))
  set p_prog := (Memory.spec 0).clientResult s (iterate bufEnsureStepProg L.toCtx L.cTab (0, rKey))
  set p_pure := bufEnsurePath L.bChar rKey L.cTab 0 (extractBufTrie L s.mem) 0
  set tr1 := p_pure.1
  set leaf := p_pure.2
  have hleaf_mn : leaf < L.maxNodes := by omega
  have hleaf_pb : leaf < 2 ^ L.ptrB := hleaf_mn.trans hvL.2.2.2.2.2.2.2.1
  have hia1_eq : tr1.itemAlloc = (extractBufTrie L s.mem).itemAlloc := by
    have hpres : ∀ m off cur (t : BufTrie), (bufEnsurePath L.bChar rKey m off t cur).1.itemAlloc =
        t.itemAlloc := by
      intro m; induction m with
      | zero => intro _ _ _; rfl
      | succ m ihm =>
        intro off cur t; dsimp only [bufEnsurePath]
        split_ifs <;> exact ihm _ _ _
    exact hpres L.cTab 0 0 _
  have hid1_read : readPacked (L.metaBase + L.offNode) L.ptrB L.w s₁.mem (6 * leaf + 2) =
      tr1.nodeLeafItem leaf := by
    have : (extractBufTrie L s₁.mem).nodeLeafItem leaf = tr1.nodeLeafItem leaf :=
      congrArg (fun t => t.nodeLeafItem leaf) hext1
    simpa only [extractBufTrie, hleaf_mn, ↓reduceIte] using this
  have h1_pb : 1 < 2 ^ L.ptrB := lt_of_le_of_lt hvL.2.2.2.2.2.2.1 hvL.2.2.2.2.2.2.2.1
  have hst_bind : (Memory.spec 0).clientState s
      (bufInsertBoundedProg (L.toCtx, (rKey, (bkt, loc)))) =
      (Memory.spec 0).clientState s₁ (bufAttachLeafProg (L.toCtx, (leaf, (bkt, loc)))) := by
    unfold bufInsertBoundedProg bufEnsureLoopProg
    have hct : trieCt L.toCtx = L.cTab := rfl
    dsimp only
    rw [hct, pure_bind, StateTransitionSpec.clientState_bind]
    change (Memory.spec 0).clientState s₁
      (bufAttachLeafProg (L.toCtx, (p_prog.1, (bkt, loc)))) = _
    rw [hr1]
  have hcost_bind : memoryCost (bufInsertBoundedProg (L.toCtx, (rKey, (bkt, loc)))) s =
      memoryCost (iterate bufEnsureStepProg L.toCtx L.cTab (0, rKey)) s +
        memoryCost (bufAttachLeafProg (L.toCtx, (leaf, (bkt, loc)))) s₁ := by
    unfold bufInsertBoundedProg bufEnsureLoopProg
    have hct : trieCt L.toCtx = L.cTab := rfl
    dsimp only
    rw [hct, pure_bind, Realization.memoryCost_bind']
    change _ + memoryCost (bufAttachLeafProg (L.toCtx, (p_prog.1, (bkt, loc)))) s₁ = _
    rw [hr1]
  dsimp only
  rw [hst_bind, hcost_bind]
  by_cases hid1_0 : tr1.nodeLeafItem leaf = 0
  · set id := tr1.itemAlloc
    have hia_lt : (extractBufTrie L s.mem).itemAlloc < L.qMax := by
      rcases hia_or with hlt | ⟨_, hne⟩
      · exact hlt
      · have hlk := hv.lookup_eq hk
        rw [← hlk] at hne
        unfold bufLookup at hne
        cases hwk : bufWalk L.bChar (extractBufTrie L s.mem).trieChild rKey L.cTab 0 0 with
        | none => rw [hwk] at hne; exact absurd rfl hne
        | some lf =>
          rw [hwk] at hne; dsimp only at hne
          have hli_nz : (extractBufTrie L s.mem).nodeLeafItem lf ≠ 0 := by
            intro h0; simp [h0] at hne
          have hp := bufEnsurePath_eq_of_walk_some L.cTab 0 (extractBufTrie L s.mem) 0 lf hwk
          have h1 : tr1 = extractBufTrie L s.mem := congrArg Prod.fst hp
          have h2 : leaf = lf := congrArg Prod.snd hp
          rw [h1, h2] at hid1_0
          exact absurd hid1_0 hli_nz
    have hid_qm : id < L.qMax := by dsimp only [id]; omega
    have hid1_pb : id + 1 < 2 ^ L.ptrB :=
      (by omega : id + 1 ≤ L.qMax).trans_lt hvL.2.2.2.2.2.2.2.2.1
    have hid_read : readPacked (L.metaBase + L.offItem) L.ptrB L.w s₁.mem (6 * L.qMax + 1) = id :=
      congrArg BufTrie.itemAlloc hext1
    set m1 := writePacked (L.metaBase + L.offItem) L.ptrB L.w s₁.mem (6 * L.qMax + 1) (id + 1)
      with hm1_def
    set m2 := writePacked (L.metaBase + L.offNode) L.ptrB L.w m1 (6 * leaf + 2) (id + 1)
      with hm2_def
    set m3 := writePacked (L.metaBase + L.offNode) L.ptrB L.w m2 (6 * leaf + 3) 1 with hm3_def
    set m4 := writePacked (L.metaBase + L.offItem) L.ptrB L.w m3 (6 * id) leaf with hm4_def
    set m5 := writePacked (L.metaBase + L.offItem) L.ptrB L.w m4 (6 * id + 1) bkt with hm5_def
    set m6 := writePacked (L.metaBase + L.offItem) L.ptrB L.w m5 (6 * id + 2) loc with hm6_def
    obtain ⟨he1, ho1⟩ := extractBufTrie_writeHeader (isItem := 1) hvL_tight (by decide) hid1_pb
      (mem := s₁.mem)
    obtain ⟨he2, ho2⟩ := extractBufTrie_writeNodeField (fld := 2) hvL_tight hleaf_mn (by decide)
      hid1_pb (mem := m1)
    obtain ⟨he3, ho3⟩ := extractBufTrie_writeNodeField (fld := 3) hvL_tight hleaf_mn (by decide)
      h1_pb (mem := m2)
    obtain ⟨he4, ho4⟩ := extractBufTrie_writeItemField (fld := 0) hvL_tight hid_qm (by decide)
      hleaf_pb (mem := m3)
    obtain ⟨he5, ho5⟩ := extractBufTrie_writeItemField (fld := 1) hvL_tight hid_qm (by decide)
      hbkt (mem := m4)
    obtain ⟨he6, ho6⟩ := extractBufTrie_writeItemField (fld := 2) hvL_tight hid_qm (by decide)
      hloc (mem := m5)
    simp only [Nat.succ_ne_zero, ↓reduceIte] at he1
    simp only [Nat.add_zero] at he4
    have hatt_st : (Memory.spec 0).clientState s₁
        (bufAttachLeafProg (L.toCtx, (leaf, (bkt, loc)))) = ⟨m6, s₁.frontier⟩ := by
      unfold bufAttachLeafProg; dsimp only [TrieLayout.toCtx]
      simp only [hleaf_mn, ↓reduceIte, prog_runClient_state_bind,
        StateTransitionSpec.clientState, runClient_state_readPackedCompGenProg,
        clientResult_readPackedCompGenProg, hid1_read, hid1_0, hid_read, hid_qm,
        runClient_state_writePackedCompGenProg]
      rw [← hm1_def, ← hm2_def, ← hm3_def, ← hm4_def, ← hm5_def, ← hm6_def]
    have hatt_cost : memoryCost (bufAttachLeafProg (L.toCtx, (leaf, (bkt, loc)))) s₁ ≤ 32 := by
      unfold bufAttachLeafProg; dsimp only [TrieLayout.toCtx]
      simp only [hleaf_mn, ↓reduceIte, Realization.memoryCost_bind',
        memoryCost_readPackedCompGenProg, StateTransitionSpec.clientState,
        runClient_state_readPackedCompGenProg, clientResult_readPackedCompGenProg,
        hid1_read, hid1_0, hid_read, hid_qm, memoryCost_writePackedCompGenProg,
        runClient_state_writePackedCompGenProg]
      omega
    set bt1 : BufTrie := { tr1 with itemAlloc := id + 1 }
    have hbt1 : extractBufTrie L m1 = bt1 := by rw [hm1_def, he1, hext1]
    set bt2 : BufTrie := { bt1 with nodeLeafItem := Function.update bt1.nodeLeafItem leaf (id + 1) }
    have hbt2 : extractBufTrie L m2 = bt2 := by rw [hm2_def, he2, hbt1]; rfl
    set bt3 : BufTrie := { bt2 with nodeActive := Function.update bt2.nodeActive leaf 1 }
    have hbt3 : extractBufTrie L m3 = bt3 := by rw [hm3_def, he3, hbt2]; rfl
    set bt4 : BufTrie := { bt3 with itemLeaf := Function.update bt3.itemLeaf id leaf }
    have hbt4 : extractBufTrie L m4 = bt4 := by rw [hm4_def, he4, hbt3]
    set bt5 : BufTrie := { bt4 with itemBucket := Function.update bt4.itemBucket id bkt }
    have hbt5 : extractBufTrie L m5 = bt5 := by rw [hm5_def, he5, hbt4]; rfl
    have hext_fin : extractBufTrie L m6 =
        bufInsert L.cTab L.bChar (extractBufTrie L s.mem) rKey bkt loc := by
      rw [hm6_def, he6, hbt5]
      unfold bufInsert
      change _ = (let p := p_pure; _)
      dsimp only
      change _ = (if tr1.nodeLeafItem leaf = 0 then _ else _)
      simp only [hid1_0, ↓reduceIte]
      dsimp only [id, bt5, bt4, bt3, bt2, bt1]
    refine ⟨by rw [hatt_st]; exact hfr1, by omega, by rw [hatt_st]; exact hext_fin, ?_, ?_⟩
    · rw [hatt_st, hext_fin]
      exact (hv.insert_spec hk).1
    · intro addr ha
      rw [hatt_st]
      exact (ho6 addr ha).trans ((ho5 addr ha).trans ((ho4 addr ha).trans
        ((ho3 addr ha).trans ((ho2 addr ha).trans ((ho1 addr ha).trans (hout1 addr ha))))))
  · have hli_orig : (extractBufTrie L s.mem).nodeLeafItem leaf = tr1.nodeLeafItem leaf ∧
        leaf < (extractBufTrie L s.mem).nodeAlloc := by
      have hpres2 : ∀ m off cur (t : BufTrie),
          cur < t.nodeAlloc →
          (∀ v c, t.trieChild v c ≠ 0 → t.trieChild v c < t.nodeAlloc) →
          (bufEnsurePath L.bChar rKey m off t cur).1.nodeLeafItem
            (bufEnsurePath L.bChar rKey m off t cur).2 ≠ 0 →
          t.nodeLeafItem (bufEnsurePath L.bChar rKey m off t cur).2 =
            (bufEnsurePath L.bChar rKey m off t cur).1.nodeLeafItem
              (bufEnsurePath L.bChar rKey m off t cur).2 ∧
            (bufEnsurePath L.bChar rKey m off t cur).2 < t.nodeAlloc := by
        intro m; induction m with
        | zero => intro _ cur t hc _ _; exact ⟨rfl, hc⟩
        | succ m ihm =>
          intro off cur t hc hch_t hnz
          dsimp only [bufEnsurePath] at hnz ⊢
          set ch0 := laneGet L.bChar rKey off
          by_cases h0 : t.trieChild cur ch0 = 0
          · simp only [h0, ↓reduceIte] at hnz ⊢
            set t1 : BufTrie :=
              { t with
                nodeAlloc := t.nodeAlloc + 1
                trieChild := Function.update t.trieChild cur
                  (Function.update (t.trieChild cur) ch0 t.nodeAlloc)
                nodeParent := Function.update t.nodeParent t.nodeAlloc cur
                nodeChar := Function.update t.nodeChar t.nodeAlloc ch0
                nodeLeafItem := Function.update t.nodeLeafItem t.nodeAlloc 0 }
            have hch_t1 : ∀ v c, t1.trieChild v c ≠ 0 → t1.trieChild v c < t1.nodeAlloc := by
              intro v c hvc; dsimp only [t1] at hvc ⊢
              by_cases hv_e : v = cur
              · subst hv_e
                by_cases hc_e : c = ch0
                · subst hc_e; simp
                · simp only [Function.update_self, Function.update_of_ne hc_e] at hvc ⊢
                  exact (hch_t v c hvc).trans (Nat.lt_succ_self _)
              · simp only [Function.update_of_ne hv_e] at hvc ⊢
                exact (hch_t v c hvc).trans (Nat.lt_succ_self _)
            obtain ⟨heq1, hlt1⟩ := ihm (off + 1) t.nodeAlloc t1 (Nat.lt_succ_self _) hch_t1 hnz
            change Function.update t.nodeLeafItem t.nodeAlloc 0
              (bufEnsurePath L.bChar rKey m (off + 1) t1 t.nodeAlloc).2 = _ at heq1
            change (bufEnsurePath L.bChar rKey m (off + 1) t1 t.nodeAlloc).2 < t.nodeAlloc + 1
              at hlt1
            by_cases heq_u : (bufEnsurePath L.bChar rKey m (off + 1) t1 t.nodeAlloc).2 =
                t.nodeAlloc
            · have hnz' := hnz
              rw [heq_u] at hnz'
              rw [heq_u, Function.update_self] at heq1
              exact absurd heq1.symm hnz'
            · rw [Function.update_of_ne heq_u] at heq1; exact ⟨heq1, by omega⟩
          · simp only [h0, ↓reduceIte] at hnz ⊢
            exact ihm (off + 1) _ t (hch_t cur ch0 h0) hch_t hnz
      exact hpres2 L.cTab 0 0 _ (by omega) hchild_lt hid1_0
    have hid1_le : tr1.nodeLeafItem leaf ≤ (extractBufTrie L s.mem).itemAlloc := by
      rw [← hli_orig.1]
      exact hleaf_inv leaf hli_orig.2 (hli_orig.1 ▸ hid1_0)
    set id := tr1.nodeLeafItem leaf - 1
    have hia_le : (extractBufTrie L s.mem).itemAlloc ≤ L.qMax :=
      hia_or.elim Nat.le_of_lt And.left
    have hid_qm : id < L.qMax := by dsimp only [id]; omega
    set m1 := writePacked (L.metaBase + L.offNode) L.ptrB L.w s₁.mem (6 * leaf + 3) 1 with hm1_def
    set m2 := writePacked (L.metaBase + L.offItem) L.ptrB L.w m1 (6 * id + 1) bkt with hm2_def
    set m3 := writePacked (L.metaBase + L.offItem) L.ptrB L.w m2 (6 * id + 2) loc with hm3_def
    obtain ⟨he1, ho1⟩ := extractBufTrie_writeNodeField (fld := 3) hvL_tight hleaf_mn (by decide)
      h1_pb (mem := s₁.mem)
    obtain ⟨he2, ho2⟩ := extractBufTrie_writeItemField (fld := 1) hvL_tight hid_qm (by decide)
      hbkt (mem := m1)
    obtain ⟨he3, ho3⟩ := extractBufTrie_writeItemField (fld := 2) hvL_tight hid_qm (by decide)
      hloc (mem := m2)
    have hatt_st : (Memory.spec 0).clientState s₁
        (bufAttachLeafProg (L.toCtx, (leaf, (bkt, loc)))) = ⟨m3, s₁.frontier⟩ := by
      unfold bufAttachLeafProg; dsimp only [TrieLayout.toCtx]
      simp only [hleaf_mn, ↓reduceIte, prog_runClient_state_bind,
        StateTransitionSpec.clientState, runClient_state_readPackedCompGenProg,
        clientResult_readPackedCompGenProg, hid1_read, hid1_0, pure_bind, id, hid_qm,
        runClient_state_writePackedCompGenProg]
      rw [← hm1_def, ← hm2_def, ← hm3_def]
    have hatt_cost : memoryCost (bufAttachLeafProg (L.toCtx, (leaf, (bkt, loc)))) s₁ ≤ 16 := by
      unfold bufAttachLeafProg; dsimp only [TrieLayout.toCtx]
      simp only [hleaf_mn, ↓reduceIte, Realization.memoryCost_bind',
        memoryCost_readPackedCompGenProg, StateTransitionSpec.clientState,
        runClient_state_readPackedCompGenProg, clientResult_readPackedCompGenProg,
        hid1_read, hid1_0, pure_bind, id, hid_qm, memoryCost_writePackedCompGenProg,
        runClient_state_writePackedCompGenProg]
      omega
    set bt1 : BufTrie := { tr1 with nodeActive := Function.update tr1.nodeActive leaf 1 }
    have hbt1 : extractBufTrie L m1 = bt1 := by rw [hm1_def, he1, hext1]; rfl
    set bt2 : BufTrie := { bt1 with itemBucket := Function.update bt1.itemBucket id bkt }
    have hbt2 : extractBufTrie L m2 = bt2 := by rw [hm2_def, he2, hbt1]; rfl
    have hext_fin : extractBufTrie L m3 =
        bufInsert L.cTab L.bChar (extractBufTrie L s.mem) rKey bkt loc := by
      rw [hm3_def, he3, hbt2]
      unfold bufInsert
      change _ = (let p := p_pure; _)
      dsimp only
      change _ = (if tr1.nodeLeafItem leaf = 0 then _ else _)
      simp only [hid1_0, ↓reduceIte]
      dsimp only [id, bt2, bt1]
    refine ⟨by rw [hatt_st]; exact hfr1, by omega, by rw [hatt_st]; exact hext_fin, ?_, ?_⟩
    · rw [hatt_st, hext_fin]
      exact (hv.insert_spec hk).1
    · intro addr ha
      rw [hatt_st]
      exact (ho3 addr ha).trans ((ho2 addr ha).trans ((ho1 addr ha).trans (hout1 addr ha)))

/-- Exact refinement and frame theorem for `bufInsertBoundedProg`. -/
theorem bufInsertBoundedProg_spec {L : TrieLayout} {s : Memory.State}
    (hvL : L.Valid L.w s.frontier)
    {mapFn : ℕ → Option (ℕ × ℕ)}
    (hv : ValidBufTrie L.cTab L.bChar (extractBufTrie L s.mem) mapFn)
    (hraw : RawBufTrieBounds (extractBufTrie L s.mem))
    (hna : (extractBufTrie L s.mem).nodeAlloc + L.cTab ≤ L.maxNodes)
    (hia : (extractBufTrie L s.mem).itemAlloc < L.qMax)
    {rKey bkt loc : ℕ} (hk : rKey < 2 ^ (L.cTab * L.bChar))
    (hbkt : bkt < 2 ^ L.ptrB) (hloc : loc < 2 ^ L.ptrB) :
    let s' := (Memory.spec 0).clientState s (bufInsertBoundedProg (L.toCtx, (rKey, (bkt, loc))))
    s'.frontier = s.frontier ∧
    memoryCost (bufInsertBoundedProg (L.toCtx, (rKey, (bkt, loc)))) s ≤ 24 * L.cTab + 32 ∧
    extractBufTrie L s'.mem = bufInsert L.cTab L.bChar (extractBufTrie L s.mem) rKey bkt loc ∧
    ValidBufTrie L.cTab L.bChar (extractBufTrie L s'.mem)
      (Function.update mapFn rKey (some (bkt, loc))) ∧
    ∀ addr, ¬L.OwnsAddr addr → s'.mem addr = s.mem addr :=
  bufInsertBoundedProg_spec_core hvL hv hraw hna (Or.inl hia) hk hbkt hloc

/-- In-place update variant of `bufInsertBoundedProg_spec` valid even at `itemAlloc = L.qMax`
when updating an already-active key `mapFn rKey ≠ none`. -/
theorem bufInsertBoundedProg_update_spec {L : TrieLayout} {s : Memory.State}
    (hvL : L.Valid L.w s.frontier)
    {mapFn : ℕ → Option (ℕ × ℕ)}
    (hv : ValidBufTrie L.cTab L.bChar (extractBufTrie L s.mem) mapFn)
    (hraw : RawBufTrieBounds (extractBufTrie L s.mem))
    (hna : (extractBufTrie L s.mem).nodeAlloc + L.cTab ≤ L.maxNodes)
    (hia : (extractBufTrie L s.mem).itemAlloc ≤ L.qMax)
    {rKey bkt loc : ℕ} (hact : mapFn rKey ≠ none)
    (hk : rKey < 2 ^ (L.cTab * L.bChar))
    (hbkt : bkt < 2 ^ L.ptrB) (hloc : loc < 2 ^ L.ptrB) :
    let s' := (Memory.spec 0).clientState s (bufInsertBoundedProg (L.toCtx, (rKey, (bkt, loc))))
    s'.frontier = s.frontier ∧
    memoryCost (bufInsertBoundedProg (L.toCtx, (rKey, (bkt, loc)))) s ≤ 24 * L.cTab + 32 ∧
    extractBufTrie L s'.mem = bufInsert L.cTab L.bChar (extractBufTrie L s.mem) rKey bkt loc ∧
    ValidBufTrie L.cTab L.bChar (extractBufTrie L s'.mem)
      (Function.update mapFn rKey (some (bkt, loc))) ∧
    ∀ addr, ¬L.OwnsAddr addr → s'.mem addr = s.mem addr :=
  bufInsertBoundedProg_spec_core hvL hv hraw hna (Or.inr ⟨hia, hact⟩) hk hbkt hloc

/-- `bufCheckSlot` in `Memory.Prog`, returning `(activeFlag, (bkt, loc))` (`RealizesBounded .exact`,
`¬ReadsWidth`). -/
def bufCheckSlotBoundedProg : TrieCtx × ℕ → Memory.Prog (ℕ × (ℕ × ℕ))
  | ((((mb, _oc), (on_, oi)), ((pb, wv), ((_ct, _bc), (mn, qm)))), id) => do
    let ia ← readPackedCompGenProg (((mb, oi), (pb, wv)), 6 * qm + 1)
    if id < ia then
      if id < qm then do
        let leaf ← readPackedCompGenProg (((mb, oi), (pb, wv)), 6 * id)
        if leaf < mn then do
          let li ← readPackedCompGenProg (((mb, on_), (pb, wv)), 6 * leaf + 2)
          let act ← readPackedCompGenProg (((mb, on_), (pb, wv)), 6 * leaf + 3)
          if li = id + 1 then
            if act = 0 then pure (0, (0, 0))
            else do
              let bkt ← readPackedCompGenProg (((mb, oi), (pb, wv)), 6 * id + 1)
              let loc ← readPackedCompGenProg (((mb, oi), (pb, wv)), 6 * id + 2)
              pure (1, (bkt, loc))
          else pure (0, (0, 0))
        else pure (0, (0, 0))
      else pure (0, (0, 0))
    else pure (0, (0, 0))

theorem realizesBounded_bufCheckSlot :
    RealizesBounded .exact bufCheckSlotBoundedProg
      (WordEncoding.encode (α := TrieCtx × ℕ))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      BufLookupPre (fun _ _ => 0) := by
  have hrp := realizesBounded_readPackedCompGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨mb, oc⟩, ⟨on_, oi⟩⟩, ⟨⟨pb, wv⟩, ⟨⟨ct, bc⟩, ⟨mn, qm⟩⟩⟩⟩, id⟩
    dsimp only [BufLookupPre, TrieLayout.ofCtx] at h
    obtain ⟨hw, hwv, hpb, _, _, _, hmn1, _, hqm_pb, _, _, h6m, h6q, hd1, hd2, hfr⟩ := h
    subst hwv
    try dsimp only [Fits] at *
    try simp only [StateTransitionSpec.clientState, runClient_state_readPackedCompGenProg] at *
    have h1_lt : 1 < 2 ^ w := Nat.one_lt_two_pow hw.ne'
    have hqm_w : qm < 2 ^ w := hqm_pb.trans_le (Nat.pow_le_pow_right (by decide) hpb))
  all_goals try exact h1_lt
  all_goals try (refine ⟨6 * mn, hw, rfl, hpb, by omega, by omega⟩)
  all_goals try (refine ⟨6 * qm + 6, hw, rfl, hpb, by omega, by omega⟩)
  all_goals omega

theorem bufCheckSlotBoundedProg_spec {L : TrieLayout} {s : Memory.State}
    (hvL : L.Valid L.w s.frontier)
    (hia_le : (extractBufTrie L s.mem).itemAlloc ≤ L.qMax) (id : ℕ) :
    (Memory.spec 0).clientState s (bufCheckSlotBoundedProg (L.toCtx, id)) = s ∧
    memoryCost (bufCheckSlotBoundedProg (L.toCtx, id)) s ≤ 12 ∧
    (Memory.spec 0).clientResult s (bufCheckSlotBoundedProg (L.toCtx, id)) =
      match bufCheckSlot (extractBufTrie L s.mem) id with
      | none => (0, (0, 0))
      | some (b, loc) => (1, (b, loc)) := by
  have _ := hvL
  unfold bufCheckSlotBoundedProg bufCheckSlot
  dsimp only [TrieLayout.toCtx]
  set tr := extractBufTrie L s.mem
  have hia_def : readPacked (L.metaBase + L.offItem) L.ptrB L.w s.mem (6 * L.qMax + 1) =
      tr.itemAlloc := rfl
  by_cases hid_ia : id < tr.itemAlloc
  · have hid_qm : id < L.qMax := hid_ia.trans_le hia_le
    set leaf := readPacked (L.metaBase + L.offItem) L.ptrB L.w s.mem (6 * id)
    have hleaf_eq : tr.itemLeaf id = leaf := by
      simp only [tr, extractBufTrie, hid_qm, ↓reduceIte, leaf]
    have hbkt_eq : tr.itemBucket id =
        readPacked (L.metaBase + L.offItem) L.ptrB L.w s.mem (6 * id + 1) := by
      simp only [tr, extractBufTrie, hid_qm, ↓reduceIte]
    have hloc_eq : tr.itemLoc id =
        readPacked (L.metaBase + L.offItem) L.ptrB L.w s.mem (6 * id + 2) := by
      simp only [tr, extractBufTrie, hid_qm, ↓reduceIte]
    by_cases hleaf : leaf < L.maxNodes
    · set li := readPacked (L.metaBase + L.offNode) L.ptrB L.w s.mem (6 * leaf + 2)
      set act := readPacked (L.metaBase + L.offNode) L.ptrB L.w s.mem (6 * leaf + 3)
      have hli_eq : tr.nodeLeafItem leaf = li := by
        simp only [tr, extractBufTrie, hleaf, ↓reduceIte, li]
      have hact_eq : tr.nodeActive leaf = act := by
        simp only [tr, extractBufTrie, hleaf, ↓reduceIte, act]
      by_cases hli : li = id + 1
      · by_cases hact0 : act = 0
        · refine ⟨?_, ?_, ?_⟩
          · unfold StateTransitionSpec.clientState
            simp [hia_def, hid_ia, hid_qm, leaf, hleaf, li, hli, act, hact0]
          · simp only [Realization.memoryCost_bind', memoryCost_readPackedCompGenProg,
              StateTransitionSpec.clientState, runClient_state_readPackedCompGenProg,
              clientResult_readPackedCompGenProg, hia_def, hid_ia, hid_qm, ↓reduceIte,
              leaf, hleaf, li, hli, act, hact0, memoryCost_pure]
            omega
          · simp [hia_def, hid_ia, hid_qm, hleaf_eq, leaf, hleaf, hli_eq, li, hli, hact_eq, act,
              hact0]
        · refine ⟨?_, ?_, ?_⟩
          · unfold StateTransitionSpec.clientState
            simp [hia_def, hid_ia, hid_qm, leaf, hleaf, li, hli, act, hact0]
          · simp only [Realization.memoryCost_bind', memoryCost_readPackedCompGenProg,
              StateTransitionSpec.clientState, runClient_state_readPackedCompGenProg,
              clientResult_readPackedCompGenProg, hia_def, hid_ia, hid_qm, ↓reduceIte,
              leaf, hleaf, li, hli, act, hact0, memoryCost_pure]
            omega
          · simp [hia_def, hid_ia, hid_qm, hleaf_eq, leaf, hleaf, hli_eq, li, hli, hact_eq, act,
              hact0, hbkt_eq, hloc_eq]
      · refine ⟨?_, ?_, ?_⟩
        · unfold StateTransitionSpec.clientState
          simp [hia_def, hid_ia, hid_qm, leaf, hleaf, li, hli]
        · simp only [Realization.memoryCost_bind', memoryCost_readPackedCompGenProg,
            StateTransitionSpec.clientState, runClient_state_readPackedCompGenProg,
            clientResult_readPackedCompGenProg, hia_def, hid_ia, hid_qm, ↓reduceIte,
            leaf, hleaf, li, hli, memoryCost_pure]
          omega
        · simp [hia_def, hid_ia, hid_qm, hleaf_eq, leaf, hleaf, hli_eq, li, hli]
    · have hli0 : tr.nodeLeafItem leaf = 0 := by simp only [tr, extractBufTrie, hleaf, ↓reduceIte]
      refine ⟨?_, ?_, ?_⟩
      · unfold StateTransitionSpec.clientState; simp [hia_def, hid_ia, hid_qm, leaf, hleaf]
      · simp only [Realization.memoryCost_bind', memoryCost_readPackedCompGenProg,
          StateTransitionSpec.clientState, runClient_state_readPackedCompGenProg,
          clientResult_readPackedCompGenProg, hia_def, hid_ia, hid_qm, ↓reduceIte,
          leaf, hleaf, memoryCost_pure]
        omega
      · simp [hia_def, hid_ia, hid_qm, hleaf_eq, leaf, hleaf, hli0]
  · refine ⟨?_, ?_, ?_⟩
    · unfold StateTransitionSpec.clientState; simp [hia_def, hid_ia]
    · simp only [Realization.memoryCost_bind', memoryCost_readPackedCompGenProg,
        StateTransitionSpec.clientState, runClient_state_readPackedCompGenProg,
        clientResult_readPackedCompGenProg, hia_def, hid_ia, ↓reduceIte, memoryCost_pure]
      omega
    · simp [hia_def, hid_ia]

/-- Single step `bufClearOne` in `Memory.Prog` (`RealizesBounded .exact`, `¬ReadsWidth`). -/
private def bufClearOneBoundedProg : TrieCtx × ℕ → Memory.Prog ℕ
  | ((((mb, oc), (on_, oi)), ((pb, wv), ((_ct, bc), (mn, qm)))), _dummy) => do
    let na ← readPackedCompGenProg (((mb, oi), (pb, wv)), 6 * qm)
    if 1 < na then do
      let u ← pure (na - 1)
      if u < mn then do
        let p ← readPackedCompGenProg (((mb, on_), (pb, wv)), 6 * u)
        let ch ← readPackedCompGenProg (((mb, on_), (pb, wv)), 6 * u + 1)
        if p < mn then
          if ch < (1 <<< bc) then
            writePackedCompGenProg ((((mb, oc), (pb, wv)), (p <<< bc) + ch), 0)
          else pure ()
        else pure ()
        writePackedCompGenProg ((((mb, on_), (pb, wv)), 6 * u + 2), 0)
        writePackedCompGenProg ((((mb, oi), (pb, wv)), 6 * qm), u)
        writePackedCompGenProg ((((mb, oi), (pb, wv)), 6 * qm + 1), 0)
        pure 0
      else pure 0
    else do
      writePackedCompGenProg ((((mb, oi), (pb, wv)), 6 * qm), 1)
      writePackedCompGenProg ((((mb, oi), (pb, wv)), 6 * qm + 1), 0)
      writePackedCompGenProg ((((mb, on_), (pb, wv)), 2), 0)
      pure 0

private theorem memoryCost_bufClearOneBoundedProg_pos (x : TrieCtx × ℕ) (s : Memory.State) :
    1 ≤ memoryCost (bufClearOneBoundedProg x) s := by
  rcases x with ⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩⟩, _⟩
  unfold bufClearOneBoundedProg
  simp only [Realization.memoryCost_bind', memoryCost_readPackedCompGenProg]
  omega

private def BufClearOnePre (w : ℕ) : TrieCtx × ℕ → Memory.State → Prop
  | (ctx, _dummy), s => (TrieLayout.ofCtx ctx).Valid w s.frontier

private theorem realizesBounded_bufClearOne :
    RealizesBounded .exact bufClearOneBoundedProg
      (WordEncoding.encode (α := TrieCtx × ℕ))
      (WordEncoding.encode (α := ℕ))
      BufClearOnePre (fun _ _ => 0) := by
  have hrp := realizesBounded_readPackedCompGen
  have hwp := realizesBounded_writePackedCompGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨mb, oc⟩, ⟨on_, oi⟩⟩, ⟨⟨pb, wv⟩, ⟨⟨ct, bc⟩, ⟨mn, qm⟩⟩⟩⟩, _⟩
    dsimp only [BufClearOnePre, TrieLayout.ofCtx] at h
    obtain ⟨hw, hwv, hpb, _, hbc, _, hmn1, hmn_pb, _, _, hmc, h6m, h6q, hd1, hd2, hfr⟩ := h
    subst hwv
    try dsimp only [Fits] at *
    try simp only [Nat.shiftLeft_eq 1, one_mul, StateTransitionSpec.clientState,
      runClient_state_readPackedCompGenProg, runClient_state_writePackedCompGenProg,
      clientResult_readPackedCompGenProg] at *
    have h1_lt : 1 < 2 ^ w := Nat.one_lt_two_pow hw.ne'
    have h6_lt : 6 < 2 ^ w := (Nat.le_mul_of_pos_right 6 hmn1).trans_lt h6m
    have hpow_bc : 2 ^ bc < 2 ^ w := Nat.pow_lt_pow_right Nat.one_lt_two hbc
    have hbc_w : bc < 2 ^ w := hbc.trans Nat.lt_two_pow_self
    have hmn_w : mn < 2 ^ w := hmn_pb.trans_le (Nat.pow_le_pow_right (by decide) hpb)
    have hna_w : readPacked (mb + oi) pb w s.mem (6 * qm) < 2 ^ w :=
      (readPacked_lt _ _ _ _ _).trans_le (Nat.pow_le_pow_right (by decide) hpb))
  all_goals try omega
  all_goals try exact ⟨6 * mn, hw, rfl, hpb, by omega,
    show mb + on_ + packedWords (6 * mn) pb w ≤ s.frontier by omega⟩
  all_goals try exact ⟨6 * qm + 6, hw, rfl, hpb, by omega,
    show mb + oi + packedWords (6 * qm + 6) pb w ≤ s.frontier by omega⟩
  all_goals (
    have hsh := child_idx_lt ‹_ < mn› ‹_ < 2 ^ bc›
    try omega
    try exact ⟨mn * 2 ^ bc, hw, rfl, hpb, hsh,
      show mb + oc + packedWords (mn * 2 ^ bc) pb w ≤ s.frontier by omega⟩)

private def bufClearLoopProg : (TrieCtx × ℕ) × ℕ → Memory.Prog ℕ
  | ((ctx, u), k) => iterate bufClearOneBoundedProg ctx k u

private theorem realizesBounded_bufClearLoop :
    RealizesBounded .exact bufClearLoopProg
      (WordEncoding.encode (α := (TrieCtx × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((ctx, u), k) s => iterationSafe bufClearOneBoundedProg BufClearOnePre w ctx k u s)
      (fun _ _ => 0) :=
  RealizesBounded.iterate₀
    (WordEncoding.encode (α := TrieCtx))
    (WordEncoding.encode (α := ℕ))
    realizesBounded_bufClearOne
    memoryCost_bufClearOneBoundedProg_pos

/-- Execute `k` elementary `bufClearOne` steps in `Memory.Prog` (`RealizesBounded .exact`,
`¬ReadsWidth`). -/
def bufClearStepsBoundedProg : TrieCtx × ℕ → Memory.Prog Unit
  | (ctx, k) => do
    let _ ← bufClearLoopProg ((ctx, 0), k)
    pure ()

theorem realizesBounded_bufClearSteps :
    RealizesBounded .exact bufClearStepsBoundedProg
      (WordEncoding.encode (α := TrieCtx × ℕ))
      (WordEncoding.encode (α := Unit))
      BufLookupPre (fun _ _ => 0) := by
  have hloop := realizesBounded_bufClearLoop
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨mb, oc⟩, ⟨on_, oi⟩⟩, ⟨⟨pb, wv⟩, ⟨⟨ct, bc⟩, ⟨mn, qm⟩⟩⟩⟩, k⟩
    set ctx : TrieCtx := (((mb, oc), (on_, oi)), ((pb, wv), ((ct, bc), (mn, qm))))
    have hvL : (TrieLayout.ofCtx ctx).Valid w s.frontier := h
    try dsimp only [Fits] at *)
  all_goals (
    have hiter : ∀ m d0 (s₀ : Memory.State),
        (TrieLayout.ofCtx ctx).Valid w s₀.frontier →
        iterationSafe bufClearOneBoundedProg BufClearOnePre w ctx m d0 s₀ ∧
        ((Memory.spec 0).clientState s₀ (iterate bufClearOneBoundedProg ctx m d0)).frontier =
          s₀.frontier := by
      intro m; induction m with
      | zero => intro _ _ _; exact ⟨trivial, rfl⟩
      | succ m ihm =>
        intro d0 s₀ hv₀
        have hs1_fr :
            ((Memory.spec 0).clientState s₀ (bufClearOneBoundedProg (ctx, d0))).frontier =
              s₀.frontier := by
          unfold bufClearOneBoundedProg StateTransitionSpec.clientState
          dsimp only [ctx]
          simp only [prog_runClient_state_bind, runClient_state_readPackedCompGenProg]
          repeat (split_ifs <;> simp only [pure_bind, prog_runClient_state_pure,
            prog_runClient_state_bind, runClient_state_readPackedCompGenProg,
            runClient_state_writePackedCompGenProg])
        obtain ⟨hs_m, hfr_m⟩ := ihm _ _ (by rwa [hs1_fr])
        refine ⟨⟨hv₀, hs_m⟩, ?_⟩
        unfold iterate; rw [StateTransitionSpec.clientState_bind]; exact hfr_m.trans hs1_fr
    exact (hiter k 0 s hvL).1)

theorem bufClearStepsBoundedProg_spec {L : TrieLayout} (hvL : L.Valid L.w (L.metaBase + L.offItem +
    packedWords (6 * L.qMax + 6) L.ptrB L.w)) :
    ∀ (k : ℕ) (s : Memory.State),
      ClearableBufTrie (extractBufTrie L s.mem) →
      (extractBufTrie L s.mem).nodeAlloc ≤ L.maxNodes →
      let s' := (Memory.spec 0).clientState s (bufClearStepsBoundedProg (L.toCtx, k))
      s'.frontier = s.frontier ∧
      memoryCost (bufClearStepsBoundedProg (L.toCtx, k)) s ≤ 24 * k ∧
      extractBufTrie L s'.mem = bufClearSteps k (extractBufTrie L s.mem) ∧
      ClearableBufTrie (extractBufTrie L s'.mem) ∧
      ∀ addr, ¬L.OwnsAddr addr → s'.mem addr = s.mem addr := by
  have h1_pb : 1 < 2 ^ L.ptrB := lt_of_le_of_lt hvL.2.2.2.2.2.2.1 hvL.2.2.2.2.2.2.2.1
  have hone : ∀ d0 (s : Memory.State),
      (extractBufTrie L s.mem).nodeAlloc ≤ L.maxNodes →
      let s₁ := (Memory.spec 0).clientState s (bufClearOneBoundedProg (L.toCtx, d0))
      s₁.frontier = s.frontier ∧
      memoryCost (bufClearOneBoundedProg (L.toCtx, d0)) s ≤ 24 ∧
      extractBufTrie L s₁.mem = bufClearOne (extractBufTrie L s.mem) ∧
      ∀ addr, ¬L.OwnsAddr addr → s₁.mem addr = s.mem addr := by
    intro d0 s hna_le
    set tr := extractBufTrie L s.mem
    have hna_def : readPacked (L.metaBase + L.offItem) L.ptrB L.w s.mem (6 * L.qMax) =
        tr.nodeAlloc := rfl
    by_cases hgt : 1 < tr.nodeAlloc
    · set u := tr.nodeAlloc - 1
      have hu_mn : u < L.maxNodes := by omega
      have hu_pb : u < 2 ^ L.ptrB := hu_mn.trans hvL.2.2.2.2.2.2.2.1
      set p := tr.nodeParent u
      set ch := tr.nodeChar u
      have hp_read : readPacked (L.metaBase + L.offNode) L.ptrB L.w s.mem (6 * u) = p := by
        dsimp only [p, tr, extractBufTrie]; simp only [hu_mn, ↓reduceIte]
      have hch_read : readPacked (L.metaBase + L.offNode) L.ptrB L.w s.mem (6 * u + 1) = ch := by
        dsimp only [ch, tr, extractBufTrie]; simp only [hu_mn, ↓reduceIte]
      by_cases hpch : p < L.maxNodes ∧ ch < 2 ^ L.bChar
      · obtain ⟨hp_mn, hch_lt⟩ := hpch
        have hch_sh : ch < (1 <<< L.bChar) := by rwa [Nat.shiftLeft_eq, one_mul]
        set m1 := writePacked (L.metaBase + L.offChild) L.ptrB L.w s.mem ((p <<< L.bChar) + ch) 0
        set m2 := writePacked (L.metaBase + L.offNode) L.ptrB L.w m1 (6 * u + 2) 0
        set m3 := writePacked (L.metaBase + L.offItem) L.ptrB L.w m2 (6 * L.qMax) u
        set m4 := writePacked (L.metaBase + L.offItem) L.ptrB L.w m3 (6 * L.qMax + 1) 0
        obtain ⟨he1, ho1⟩ := extractBufTrie_writeChild hvL hp_mn hch_lt (Nat.two_pow_pos _)
          (mem := s.mem)
        obtain ⟨he2, ho2⟩ := extractBufTrie_writeNodeField (fld := 2) hvL hu_mn (by decide)
          (Nat.two_pow_pos _) (mem := m1)
        obtain ⟨he3, ho3⟩ := extractBufTrie_writeHeader (isItem := 0) hvL (by decide) hu_pb
          (mem := m2)
        obtain ⟨he4, ho4⟩ := extractBufTrie_writeHeader (isItem := 1) hvL (by decide)
          (Nat.two_pow_pos _) (mem := m3)
        simp only [Nat.add_zero, ↓reduceIte] at he3
        simp only [Nat.succ_ne_zero, ↓reduceIte] at he4
        have hst1 : (Memory.spec 0).clientState s (bufClearOneBoundedProg (L.toCtx, d0)) =
            ⟨m4, s.frontier⟩ := by
          unfold bufClearOneBoundedProg; dsimp only [TrieLayout.toCtx]
          simp [hna_def, hgt, u, hu_mn, hp_read, hch_read, hp_mn, hch_sh, m1, m2, m3, m4]
        have hcost1 : memoryCost (bufClearOneBoundedProg (L.toCtx, d0)) s ≤ 24 := by
          unfold bufClearOneBoundedProg; dsimp only [TrieLayout.toCtx]
          simp only [Realization.memoryCost_bind', memoryCost_readPackedCompGenProg,
            StateTransitionSpec.clientState, runClient_state_readPackedCompGenProg,
            clientResult_readPackedCompGenProg, hna_def, hgt, ↓reduceIte, pure_bind,
            u, hu_mn, hp_read, hch_read, hp_mn, hch_sh, memoryCost_writePackedCompGenProg,
            runClient_state_writePackedCompGenProg, memoryCost_pure]
          omega
        refine ⟨by rw [hst1], hcost1, ?_, fun addr ha => ?_⟩
        · rw [hst1]; dsimp only [m4, m3, m2, m1] at he4 he3 he2 he1 ⊢
          rw [he4, he3, he2, he1]
          dsimp only [u, p, ch, tr] at hgt ⊢
          unfold bufClearOne; simp only [hgt, ↓reduceIte]
        · rw [hst1]
          exact (ho4 addr ha).trans ((ho3 addr ha).trans ((ho2 addr ha).trans (ho1 addr ha)))
      · have hch_zero : tr.trieChild p ch = 0 := by
          dsimp only [tr, extractBufTrie]
          simp only [hpch, ↓reduceIte]
        have hupd_noop :
            Function.update tr.trieChild p (Function.update (tr.trieChild p) ch 0) =
              tr.trieChild := by
          have h1 : Function.update (tr.trieChild p) ch 0 = tr.trieChild p :=
            Function.update_eq_self_iff.mpr hch_zero.symm
          rw [h1]
          exact Function.update_eq_self_iff.mpr rfl
        set m2 := writePacked (L.metaBase + L.offNode) L.ptrB L.w s.mem (6 * u + 2) 0
        set m3 := writePacked (L.metaBase + L.offItem) L.ptrB L.w m2 (6 * L.qMax) u
        set m4 := writePacked (L.metaBase + L.offItem) L.ptrB L.w m3 (6 * L.qMax + 1) 0
        obtain ⟨he2, ho2⟩ := extractBufTrie_writeNodeField (fld := 2) hvL hu_mn (by decide)
          (Nat.two_pow_pos _) (mem := s.mem)
        obtain ⟨he3, ho3⟩ := extractBufTrie_writeHeader (isItem := 0) hvL (by decide) hu_pb
          (mem := m2)
        obtain ⟨he4, ho4⟩ := extractBufTrie_writeHeader (isItem := 1) hvL (by decide)
          (Nat.two_pow_pos _) (mem := m3)
        simp only [Nat.add_zero, ↓reduceIte] at he3
        simp only [Nat.succ_ne_zero, ↓reduceIte] at he4
        have hnot_sh : ¬(p < L.maxNodes ∧ ch < (1 <<< L.bChar)) := by
          rwa [Nat.shiftLeft_eq, one_mul]
        have hst1 : (Memory.spec 0).clientState s (bufClearOneBoundedProg (L.toCtx, d0)) =
            ⟨m4, s.frontier⟩ := by
          unfold bufClearOneBoundedProg; dsimp only [TrieLayout.toCtx]
          by_cases hp_mn : p < L.maxNodes
          · have hch_nsh : ¬(ch < (1 <<< L.bChar)) := fun h => hnot_sh ⟨hp_mn, h⟩
            simp [hna_def, hgt, u, hu_mn, hp_read, hch_read, hp_mn, hch_nsh, m2, m3, m4]
          · simp [hna_def, hgt, u, hu_mn, hp_read, hp_mn, m2, m3, m4]
        have hcost1 : memoryCost (bufClearOneBoundedProg (L.toCtx, d0)) s ≤ 24 := by
          unfold bufClearOneBoundedProg; dsimp only [TrieLayout.toCtx]
          by_cases hp_mn : p < L.maxNodes
          · have hch_nsh : ¬(ch < (1 <<< L.bChar)) := fun h => hnot_sh ⟨hp_mn, h⟩
            simp only [Realization.memoryCost_bind', memoryCost_readPackedCompGenProg,
              StateTransitionSpec.clientState, runClient_state_readPackedCompGenProg,
              clientResult_readPackedCompGenProg, hna_def, hgt, ↓reduceIte, pure_bind,
              u, hu_mn, hp_read, hch_read, hp_mn, hch_nsh, memoryCost_pure,
              memoryCost_writePackedCompGenProg, runClient_state_writePackedCompGenProg]
            omega
          · simp only [Realization.memoryCost_bind', memoryCost_readPackedCompGenProg,
              StateTransitionSpec.clientState, runClient_state_readPackedCompGenProg,
              clientResult_readPackedCompGenProg, hna_def, hgt, ↓reduceIte, pure_bind,
              u, hu_mn, hp_read, hp_mn, memoryCost_pure,
              memoryCost_writePackedCompGenProg, runClient_state_writePackedCompGenProg]
            omega
        refine ⟨by rw [hst1], hcost1, ?_, fun addr ha => ?_⟩
        · rw [hst1]; dsimp only [m4, m3, m2] at he4 he3 he2 ⊢
          rw [he4, he3, he2]
          dsimp only [u, p, ch, tr] at hgt hupd_noop ⊢
          unfold bufClearOne; simp only [hgt, ↓reduceIte, hupd_noop]
        · rw [hst1]
          exact (ho4 addr ha).trans ((ho3 addr ha).trans (ho2 addr ha))
    · have h0_mn : 0 < L.maxNodes := hvL.2.2.2.2.2.2.1
      set m1 := writePacked (L.metaBase + L.offItem) L.ptrB L.w s.mem (6 * L.qMax) 1
      set m2 := writePacked (L.metaBase + L.offItem) L.ptrB L.w m1 (6 * L.qMax + 1) 0
      set m3 := writePacked (L.metaBase + L.offNode) L.ptrB L.w m2 (6 * 0 + 2) 0
      obtain ⟨he1, ho1⟩ := extractBufTrie_writeHeader (isItem := 0) hvL (by decide) h1_pb
        (mem := s.mem)
      obtain ⟨he2, ho2⟩ := extractBufTrie_writeHeader (isItem := 1) hvL (by decide)
        (Nat.two_pow_pos _) (mem := m1)
      obtain ⟨he3, ho3⟩ := extractBufTrie_writeNodeField (u := 0) (fld := 2) hvL h0_mn (by decide)
        (Nat.two_pow_pos _) (mem := m2)
      simp only [Nat.add_zero, ↓reduceIte] at he1
      simp only [Nat.succ_ne_zero, ↓reduceIte] at he2
      simp only [Nat.mul_zero, Nat.zero_add] at m3 he3
      have hst1 : (Memory.spec 0).clientState s (bufClearOneBoundedProg (L.toCtx, d0)) =
          ⟨m3, s.frontier⟩ := by
        unfold bufClearOneBoundedProg; dsimp only [TrieLayout.toCtx]
        simp [hna_def, hgt, m1, m2, m3]
      have hcost1 : memoryCost (bufClearOneBoundedProg (L.toCtx, d0)) s ≤ 24 := by
        unfold bufClearOneBoundedProg; dsimp only [TrieLayout.toCtx]
        simp only [Realization.memoryCost_bind', memoryCost_readPackedCompGenProg,
          StateTransitionSpec.clientState, runClient_state_readPackedCompGenProg,
          clientResult_readPackedCompGenProg, hna_def, hgt, ↓reduceIte,
          memoryCost_writePackedCompGenProg, runClient_state_writePackedCompGenProg,
          memoryCost_pure]
        omega
      refine ⟨by rw [hst1], hcost1, ?_, fun addr ha => ?_⟩
      · rw [hst1]; dsimp only [m3, m2, m1] at he3 he2 he1 ⊢
        rw [he3, he2, he1]
        dsimp only [tr] at hgt ⊢
        unfold bufClearOne; simp only [hgt, ↓reduceIte]
      · rw [hst1]
        exact (ho3 addr ha).trans ((ho2 addr ha).trans (ho1 addr ha))
  have hloop_spec : ∀ (k d0 : ℕ) (s : Memory.State),
      ClearableBufTrie (extractBufTrie L s.mem) →
      (extractBufTrie L s.mem).nodeAlloc ≤ L.maxNodes →
      let s' := (Memory.spec 0).clientState s (iterate bufClearOneBoundedProg L.toCtx k d0)
      s'.frontier = s.frontier ∧
      memoryCost (iterate bufClearOneBoundedProg L.toCtx k d0) s ≤ 24 * k ∧
      extractBufTrie L s'.mem = bufClearSteps k (extractBufTrie L s.mem) ∧
      ClearableBufTrie (extractBufTrie L s'.mem) ∧
      ∀ addr, ¬L.OwnsAddr addr → s'.mem addr = s.mem addr := by
    intro k
    induction k with
    | zero =>
      intro _ s hc _
      exact ⟨rfl, Nat.zero_le _, rfl, hc, fun _ _ => rfl⟩
    | succ k ih =>
      intro d0 s hc hna_le
      obtain ⟨hfr1, hc1, hext1, ho1⟩ := hone d0 s hna_le
      obtain ⟨hc_nxt, hna_nxt⟩ := hc.clearOne_step
      have hna_le1 : (bufClearOne (extractBufTrie L s.mem)).nodeAlloc ≤ L.maxNodes := by
        rw [hna_nxt]; have := hvL.2.2.2.2.2.2.1; omega
      set s₁ := (Memory.spec 0).clientState s (bufClearOneBoundedProg (L.toCtx, d0))
      set d₁ := (Memory.spec 0).clientResult s (bufClearOneBoundedProg (L.toCtx, d0))
      obtain ⟨hfr_k, hc_k, hext_k, hcl_k, ho_k⟩ :=
        ih d₁ s₁ (hext1.symm ▸ hc_nxt) (hext1.symm ▸ hna_le1)
      unfold iterate
      rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind']
      refine ⟨hfr_k.trans hfr1, ?_, ?_, hcl_k,
        fun addr ha => (ho_k addr ha).trans (ho1 addr ha)⟩
      · change memoryCost (bufClearOneBoundedProg (L.toCtx, d0)) s +
          memoryCost (iterate bufClearOneBoundedProg L.toCtx k d₁) s₁ ≤ _
        omega
      · change extractBufTrie L ((Memory.spec 0).clientState s₁
          (iterate bufClearOneBoundedProg L.toCtx k d₁)).mem = _
        rw [hext_k, hext1]; rfl
  intro k s hc hna_le
  unfold bufClearStepsBoundedProg bufClearLoopProg; dsimp only
  rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
    StateTransitionSpec.clientState_pure, memoryCost_pure, add_zero]
  exact hloop_spec k 0 s hc hna_le

/-! ## Section 5: Unconditional Read-State and Frame Preservation Lemmas -/

@[simp] theorem runClient_state_bufLookupBoundedProg (x : TrieCtx × ℕ) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (bufLookupBoundedProg x)) = s := by
  rcases x with ⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨⟨_, _⟩, ⟨mn, _⟩⟩⟩⟩, rk⟩
  unfold bufLookupBoundedProg bufWalkBoundedProg bufWalkLoopProg
  dsimp only [trieMb, trieOn, trieOi, triePb, trieWv, trieCt, trieMn, trieQm]
  have hwk : ∀ c f a, (Memory.spec 0).clientState s (iterate bufWalkStepProg c f a) = s := by
    intro c f; induction f with
    | zero => intro _; rfl
    | succ f ih =>
      intro a; unfold iterate; rw [StateTransitionSpec.clientState_bind]
      have hs1 : (Memory.spec 0).clientState s (bufWalkStepProg (c, a)) = s := by
        rcases c with ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨⟨_, _⟩, ⟨mn', _⟩⟩⟩⟩
        rcases a with ⟨⟨_, cur⟩, _⟩
        unfold StateTransitionSpec.clientState bufWalkStepProg
        by_cases hc : cur < mn' <;>
          simp only [hc, ↓reduceIte, pure_bind, prog_runClient_state_bind,
            StateTransitionSpec.clientState, runClient_state_readPackedCompGenProg] <;>
          split_ifs <;> rfl
      rw [hs1]; exact ih _
  simp only [pure_bind, prog_runClient_state_bind, hwk, StateTransitionSpec.clientState,
    prog_runClient_state_pure]
  split_ifs
  · rfl
  · simp only [prog_runClient_state_bind, StateTransitionSpec.clientState,
      runClient_state_readPackedCompGenProg]
    split_ifs
    · rfl
    · rfl
    · simp only [bind_pure_comp, prog_runClient_state_bind, StateTransitionSpec.clientState,
        runClient_state_readPackedCompGenProg, prog_runClient_state_map]
    · rfl
  · rfl

theorem clientState_bufLookupBoundedProg (x : TrieCtx × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (bufLookupBoundedProg x) = s :=
  runClient_state_bufLookupBoundedProg x s

@[simp] private theorem runClient_state_bufCheckSlotBoundedProg
    (x : TrieCtx × ℕ) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (bufCheckSlotBoundedProg x)) = s := by
  rcases x with ⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩⟩, _⟩
  unfold bufCheckSlotBoundedProg
  simp only [prog_runClient_state_bind, StateTransitionSpec.clientState,
    runClient_state_readPackedCompGenProg]
  split_ifs
  · simp only [prog_runClient_state_bind, StateTransitionSpec.clientState,
      runClient_state_readPackedCompGenProg]
    split_ifs
    · simp only [prog_runClient_state_bind, StateTransitionSpec.clientState,
        runClient_state_readPackedCompGenProg]
      split_ifs
      · rfl
      · simp only [bind_pure_comp, prog_runClient_state_bind, StateTransitionSpec.clientState,
          runClient_state_readPackedCompGenProg, prog_runClient_state_map]
      · rfl
    · rfl
  · rfl
  · rfl

theorem clientState_bufCheckSlotBoundedProg (x : TrieCtx × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (bufCheckSlotBoundedProg x) = s :=
  runClient_state_bufCheckSlotBoundedProg x s

theorem bufInsertBoundedProg_frame {L : TrieLayout} {s : Memory.State}
    (hvL : L.Valid L.w s.frontier) (rKey bkt loc : ℕ) :
    let s' := (Memory.spec 0).clientState s (bufInsertBoundedProg (L.toCtx, (rKey, (bkt, loc))))
    s'.frontier = s.frontier ∧
    memoryCost (bufInsertBoundedProg (L.toCtx, (rKey, (bkt, loc)))) s ≤ 24 * L.cTab + 32 ∧
    ∀ addr, ¬L.OwnsAddr addr → s'.mem addr = s.mem addr := by
  dsimp only
  have hw : 0 < L.w := hvL.1
  obtain ⟨_, hfr1, hc1, hout1⟩ := bufEnsure_iter_safe L.cTab (0, rKey) s hvL
  set s₁ := (Memory.spec 0).clientState s (iterate bufEnsureStepProg L.toCtx L.cTab (0, rKey))
  set leaf := ((Memory.spec 0).clientResult s
    (iterate bufEnsureStepProg L.toCtx L.cTab (0, rKey))).1
  set s₂ := (Memory.spec 0).clientState s₁ (bufAttachLeafProg (L.toCtx, (leaf, (bkt, loc))))
  have hatt : s₂.frontier = s₁.frontier ∧
      memoryCost (bufAttachLeafProg (L.toCtx, (leaf, (bkt, loc)))) s₁ ≤ 32 ∧
      ∀ addr, ¬L.OwnsAddr addr → s₂.mem addr = s₁.mem addr := by
    dsimp only [s₂]; unfold bufAttachLeafProg; dsimp only [TrieLayout.toCtx]
    by_cases hl : leaf < L.maxNodes
    · simp only [hl, ↓reduceIte, StateTransitionSpec.clientState, Realization.memoryCost_bind',
        prog_runClient_state_bind, runClient_state_readPackedCompGenProg,
        memoryCost_readPackedCompGenProg, clientResult_readPackedCompGenProg]
      split_ifs with hid0
      · simp only [StateTransitionSpec.clientState, Realization.memoryCost_bind',
          prog_runClient_state_bind, runClient_state_readPackedCompGenProg,
          memoryCost_readPackedCompGenProg, clientResult_readPackedCompGenProg]
        split_ifs with hqm
        · simp only [prog_runClient_state_bind, runClient_state_writePackedCompGenProg,
            Realization.memoryCost_bind', memoryCost_writePackedCompGenProg]
          refine ⟨trivial, by omega, fun addr ha => ?_⟩
          rw [writePacked_outside hw _ (by omega : _ < 6 * L.qMax + 6) _
            (fun h => ha (Or.inr (Or.inr h)))]
          rw [writePacked_outside hw _ (by omega : _ < 6 * L.qMax + 6) _
            (fun h => ha (Or.inr (Or.inr h)))]
          rw [writePacked_outside hw _ (by omega : _ < 6 * L.qMax + 6) _
            (fun h => ha (Or.inr (Or.inr h)))]
          rw [writePacked_outside hw _ (by omega : _ < 6 * L.maxNodes) _
            (fun h => ha (Or.inr (Or.inl h)))]
          rw [writePacked_outside hw _ (by omega : _ < 6 * L.maxNodes) _
            (fun h => ha (Or.inr (Or.inl h)))]
          exact writePacked_outside hw _ (by omega : _ < 6 * L.qMax + 6) _
            (fun h => ha (Or.inr (Or.inr h)))
        · simp only [prog_runClient_state_pure, memoryCost_pure]
          exact ⟨trivial, by omega, fun _ _ => trivial⟩
      · simp only [pure_bind]
        split_ifs with hqm
        · simp only [prog_runClient_state_bind, runClient_state_writePackedCompGenProg,
            Realization.memoryCost_bind', memoryCost_writePackedCompGenProg]
          refine ⟨trivial, by omega, fun addr ha => ?_⟩
          rw [writePacked_outside hw _ (by omega : _ < 6 * L.qMax + 6) _
            (fun h => ha (Or.inr (Or.inr h)))]
          rw [writePacked_outside hw _ (by omega : _ < 6 * L.qMax + 6) _
            (fun h => ha (Or.inr (Or.inr h)))]
          exact writePacked_outside hw _ (by omega : _ < 6 * L.maxNodes) _
            (fun h => ha (Or.inr (Or.inl h)))
        · simp only [prog_runClient_state_pure, memoryCost_pure]
          exact ⟨trivial, by omega, fun _ _ => trivial⟩
    · simp only [hl, ↓reduceIte, StateTransitionSpec.clientState, prog_runClient_state_pure,
        memoryCost_pure]
      exact ⟨trivial, by omega, fun _ _ => trivial⟩
  have hct : trieCt L.toCtx = L.cTab := rfl
  unfold bufInsertBoundedProg bufEnsureLoopProg; dsimp only
  rw [hct, pure_bind, StateTransitionSpec.clientState_bind, Realization.memoryCost_bind']
  change s₂.frontier = s.frontier ∧
    memoryCost (iterate bufEnsureStepProg L.toCtx L.cTab (0, rKey)) s +
      memoryCost (bufAttachLeafProg (L.toCtx, (leaf, (bkt, loc)))) s₁ ≤ 24 * L.cTab + 32 ∧
    ∀ addr, ¬L.OwnsAddr addr → s₂.mem addr = s.mem addr
  exact ⟨hatt.1.trans hfr1, by have := hatt.2.1; omega,
    fun addr ha => (hatt.2.2 addr ha).trans (hout1 addr ha)⟩

theorem bufClearStepsBoundedProg_frame {L : TrieLayout} {fr : ℕ} (hvL : L.Valid L.w fr) :
    ∀ (k : ℕ) (s₀ : Memory.State),
      let s' := (Memory.spec 0).clientState s₀ (bufClearStepsBoundedProg (L.toCtx, k))
      s'.frontier = s₀.frontier ∧
      memoryCost (bufClearStepsBoundedProg (L.toCtx, k)) s₀ ≤ 24 * k ∧
      ∀ addr, ¬L.OwnsAddr addr → s'.mem addr = s₀.mem addr := by
  have hw : 0 < L.w := hvL.1
  have hmn1 : 1 ≤ L.maxNodes := hvL.2.2.2.2.2.2.1
  have hone : ∀ d0 (s₀ : Memory.State),
      let s₁ := (Memory.spec 0).clientState s₀ (bufClearOneBoundedProg (L.toCtx, d0))
      s₁.frontier = s₀.frontier ∧
      memoryCost (bufClearOneBoundedProg (L.toCtx, d0)) s₀ ≤ 24 ∧
      ∀ addr, ¬L.OwnsAddr addr → s₁.mem addr = s₀.mem addr := by
    intro d0 s₀; dsimp only; unfold bufClearOneBoundedProg; dsimp only [TrieLayout.toCtx]
    simp only [StateTransitionSpec.clientState, Realization.memoryCost_bind',
      prog_runClient_state_bind, runClient_state_readPackedCompGenProg,
      memoryCost_readPackedCompGenProg, clientResult_readPackedCompGenProg]
    split_ifs with hgt
    · simp only [pure_bind]
      split_ifs with hu
      · simp only [prog_runClient_state_bind, runClient_state_readPackedCompGenProg,
          Realization.memoryCost_bind', memoryCost_readPackedCompGenProg,
          clientResult_readPackedCompGenProg]
        by_cases hp : readPacked (L.metaBase + L.offNode) L.ptrB L.w s₀.mem
            (6 * (readPacked (L.metaBase + L.offItem) L.ptrB L.w s₀.mem (6 * L.qMax) - 1)) <
            L.maxNodes
        · by_cases hch : readPacked (L.metaBase + L.offNode) L.ptrB L.w s₀.mem
              (6 * (readPacked (L.metaBase + L.offItem) L.ptrB L.w s₀.mem (6 * L.qMax) - 1) + 1) <
              (1 <<< L.bChar)
          · have hch2 : readPacked (L.metaBase + L.offNode) L.ptrB L.w s₀.mem
                (6 * (readPacked (L.metaBase + L.offItem) L.ptrB L.w s₀.mem (6 * L.qMax) - 1) + 1) <
                2 ^ L.bChar := by rwa [Nat.shiftLeft_eq, one_mul] at hch
            simp only [hp, hch, ↓reduceIte, prog_runClient_state_bind,
              runClient_state_writePackedCompGenProg, prog_runClient_state_pure,
              Realization.memoryCost_bind', memoryCost_writePackedCompGenProg, memoryCost_pure]
            refine ⟨trivial, by omega, fun addr ha => ?_⟩
            rw [writePacked_outside hw _ (by omega : 6 * L.qMax + 1 < 6 * L.qMax + 6) _
              (fun h => ha (Or.inr (Or.inr h)))]
            rw [writePacked_outside hw _ (by omega : 6 * L.qMax < 6 * L.qMax + 6) _
              (fun h => ha (Or.inr (Or.inr h)))]
            rw [writePacked_outside hw _ (by omega : _ < 6 * L.maxNodes) _
              (fun h => ha (Or.inr (Or.inl h)))]
            exact writePacked_outside hw _ (child_idx_lt hp hch2) _ (fun h => ha (Or.inl h))
          · simp only [hp, hch, ↓reduceIte, prog_runClient_state_bind, prog_runClient_state_pure,
              runClient_state_writePackedCompGenProg, Realization.memoryCost_bind',
              memoryCost_writePackedCompGenProg, memoryCost_pure]
            refine ⟨trivial, by omega, fun addr ha => ?_⟩
            rw [writePacked_outside hw _ (by omega : 6 * L.qMax + 1 < 6 * L.qMax + 6) _
              (fun h => ha (Or.inr (Or.inr h)))]
            rw [writePacked_outside hw _ (by omega : 6 * L.qMax < 6 * L.qMax + 6) _
              (fun h => ha (Or.inr (Or.inr h)))]
            exact writePacked_outside hw _ (by omega : _ < 6 * L.maxNodes) _
              (fun h => ha (Or.inr (Or.inl h)))
        · simp only [hp, ↓reduceIte, prog_runClient_state_bind, prog_runClient_state_pure,
            runClient_state_writePackedCompGenProg, Realization.memoryCost_bind',
            memoryCost_writePackedCompGenProg, memoryCost_pure]
          refine ⟨trivial, by omega, fun addr ha => ?_⟩
          rw [writePacked_outside hw _ (by omega : 6 * L.qMax + 1 < 6 * L.qMax + 6) _
            (fun h => ha (Or.inr (Or.inr h)))]
          rw [writePacked_outside hw _ (by omega : 6 * L.qMax < 6 * L.qMax + 6) _
            (fun h => ha (Or.inr (Or.inr h)))]
          exact writePacked_outside hw _ (by omega : _ < 6 * L.maxNodes) _
            (fun h => ha (Or.inr (Or.inl h)))
      · simp only [prog_runClient_state_pure, memoryCost_pure]
        exact ⟨trivial, by omega, fun _ _ => trivial⟩
    · simp only [prog_runClient_state_bind, runClient_state_writePackedCompGenProg,
        prog_runClient_state_pure, Realization.memoryCost_bind',
        memoryCost_writePackedCompGenProg, memoryCost_pure]
      refine ⟨trivial, by omega, fun addr ha => ?_⟩
      rw [writePacked_outside hw _ (by omega : 2 < 6 * L.maxNodes) _
        (fun h => ha (Or.inr (Or.inl h)))]
      rw [writePacked_outside hw _ (by omega : 6 * L.qMax + 1 < 6 * L.qMax + 6) _
        (fun h => ha (Or.inr (Or.inr h)))]
      exact writePacked_outside hw _ (by omega : 6 * L.qMax < 6 * L.qMax + 6) _
        (fun h => ha (Or.inr (Or.inr h)))
  have hloop : ∀ k d0 (s₀ : Memory.State),
      let s' := (Memory.spec 0).clientState s₀ (iterate bufClearOneBoundedProg L.toCtx k d0)
      s'.frontier = s₀.frontier ∧
      memoryCost (iterate bufClearOneBoundedProg L.toCtx k d0) s₀ ≤ 24 * k ∧
      ∀ addr, ¬L.OwnsAddr addr → s'.mem addr = s₀.mem addr := by
    intro k; induction k with
    | zero => intro _ _; exact ⟨rfl, Nat.zero_le _, fun _ _ => rfl⟩
    | succ k ih =>
      intro d0 s₀
      obtain ⟨hfr1, hc1, ho1⟩ := hone d0 s₀
      obtain ⟨hfrk, hck, hok⟩ := ih _ _
      unfold iterate; rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind']
      exact ⟨hfrk.trans hfr1, by omega,
        fun addr ha => (hok addr ha).trans (ho1 addr ha)⟩
  intro k s₀
  unfold bufClearStepsBoundedProg bufClearLoopProg; dsimp only
  rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
    StateTransitionSpec.clientState_pure, memoryCost_pure, add_zero]
  exact hloop k 0 s₀

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

end
