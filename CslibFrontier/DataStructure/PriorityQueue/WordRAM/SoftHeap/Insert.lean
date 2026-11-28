/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.PriorityQueue.WordRAM.SoftHeap.Defill
public import CslibFrontier.Computability.WordRAM.Realization.Absorb
public import CslibFrontier.Computability.WordRAM.Realization.While
public import CslibFrontier.Computability.WordRAM.Realization.Loop
-- `import all` reads `Program`'s `shInsertInit`/`combine*`/`shInsertRaw`/`shInsertLinkRoot`
-- (and `shInsert` body), plus `Model`'s `InPoolRaw` and `suffixMinTree_spec` lemmas.
import all CslibFrontier.DataStructure.PriorityQueue.WordRAM.SoftHeap.Program
import all CslibFrontier.DataStructure.PriorityQueue.WordRAM.SoftHeap.Model
import CslibFrontier.Foundations.Data.Nat.HalvingRecurrence
import CslibFrontier.Computability.WordRAM.Realization.ProgFrame
import CslibFrontier.DataStructure.Memory.Frame
-- Record writes use the private `Block.mem_writeList_of_not_mem` frame lemma.
import all CslibFrontier.DataStructure.Memory.TripleFrame
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Insertion Specification for Word-RAM Soft Heaps

Proves `shInsert_spec`: inserting `(val, origKey)` into a valid soft heap preserves `SHInv`,
updates root links and suffix minima, frames writes within `InSHPool`, preserves surviving entry
keys up to non-decreasing `ckey`, and satisfies
`memoryCost + totalPhi h.rankThreshold roots' ≤
totalPhi h.rankThreshold roots + (240 * h.rankThreshold + 520)`.

## Main results

* `Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap.shInsert_spec`: full correctness,
  permutation, key-monotonicity, framing, and `O(h.rankThreshold)` amortized memory-cost
  specification for `shInsert`.
-/

public section

namespace Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure Cslib.DataStructure.Memory

private theorem pure_unit_eq : (fun _ : Unit => (pure () : Memory.Prog Unit)) = pure :=
  funext fun u => congrArg pure (Subsingleton.elim () u)

-- The item, singleton node, and combined parent occupy consecutive memory cells.
private theorem writeRecord_spec (w base : ℕ) (words : List ℕ) (s : Memory.State)
    (hbound : base + words.length ≤ s.frontier) (hfits : ∀ v ∈ words, Fits w v) :
    let p := Block.writeList base words
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p) ∧
    memoryCost p s = words.length ∧
    let s' := (Memory.spec 0).clientState s p
    s'.frontier = s.frontier ∧
    (∀ a, s'.mem a ≠ s.mem a → ∃ j < words.length, a = base + j) ∧
    Block.HoldsList base words s'.mem := by
  refine ⟨Block.validHistory_writeList w base words s hbound hfits,
    Block.totalCost_writeList 0 base words s, Block.clientState_writeList_frontier 0 base words s,
    ?_, Block.holdsList_writeList 0 base words s⟩
  intro a ha
  have ha' : a ∈ Set.Ico base (base + words.length) :=
    not_not.mp (fun h => ha (Block.mem_writeList_of_not_mem 0 base words s h))
  obtain ⟨hlo, hhi⟩ := ha'
  exact ⟨a - base, by lia, by lia⟩

private theorem shInsertInit_spec {rt w itemBase nodeBase itemIdx nodeIdx val origKey : ℕ}
    {s : Memory.State} (h16 : Fits w 16) (_hwf : Memory.WellFormed w s)
    (hi_pos : 0 < itemIdx) (hn_pos : 0 < nodeIdx)
    (hi_lt : itemBase + 3 * itemIdx + 2 < s.frontier)
    (hn_lt : nodeBase + 12 * nodeIdx + 11 < s.frontier)
    (hdisj : ∀ j < 12, ∀ k < 3, nodeBase + 12 * nodeIdx + j ≠ itemBase + 3 * itemIdx + k)
    (hi_fit : Fits w itemIdx) (hn_fit : Fits w nodeIdx)
    (he_fit : Fits w val) (hk_fit : Fits w origKey) :
    let d : Fin 6 → ℕ := ![itemBase, nodeBase, itemIdx, nodeIdx, val, origKey]
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (shInsertInit d)) ∧
    memoryCost (shInsertInit d) s = 15 ∧
    let s' := (Memory.spec 0).clientState s (shInsertInit d)
    s'.frontier = s.frontier ∧
    (∀ a, s'.mem a ≠ s.mem a →
      (∃ j < 3, a = itemBase + 3 * itemIdx + j) ∨
      (∃ j < 12, a = nodeBase + 12 * nodeIdx + j)) ∧
    let newIt : SHItem := ⟨itemIdx, val, origKey⟩
    let z₀ : SHTree := .node nodeIdx 0 origKey [newIt] none none
    TreeMemRep rt itemBase nodeBase s'.mem z₀ ∧
    s'.mem (nodeBase + 12 * nodeIdx + 8) = 0 ∧
    s'.mem (nodeBase + 12 * nodeIdx + 9) = 0 ∧
    s'.mem (nodeBase + 12 * nodeIdx + 10) = 0 ∧
    s'.mem (nodeBase + 12 * nodeIdx + 11) = nodeIdx := by
  have h0_fit : Fits w 0 := h16.of_le (by lia)
  have h1_fit : Fits w 1 := h16.of_le (by lia)
  let itWords := [val, origKey, 0]
  let nodeWords := [origKey, 0, 1, 1, itemIdx, itemIdx, 0, 0, 0, 0, 0, nodeIdx]
  let p_it := Block.writeList (itemBase + 3 * itemIdx) itWords
  let p_nd := Block.writeList (nodeBase + 12 * nodeIdx) nodeWords
  have hsplit : shInsertInit ![itemBase, nodeBase, itemIdx, nodeIdx, val, origKey] =
      (p_it >>= fun _ => p_nd) := by
    dsimp only [shInsertInit]
    simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    simp only [p_it, p_nd, itWords, nodeWords, Block.writeList_cons, Block.writeList_nil,
      bind_assoc, pure_unit_eq, bind_pure, Nat.add_assoc, Nat.reduceAdd]
  have hi_bound : itemBase + 3 * itemIdx + itWords.length ≤ s.frontier := by
    change itemBase + 3 * itemIdx + 3 ≤ s.frontier
    lia
  have hi_fits : ∀ v ∈ itWords, Fits w v := by
    simp only [itWords, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, he_fit, hk_fit, h0_fit]
  let s₁ := (Memory.spec 0).clientState s p_it
  obtain ⟨hv_it, hm_it, hfr₁, hs₁_mem, hs₁_hold⟩ :=
    writeRecord_spec w (itemBase + 3 * itemIdx) itWords s hi_bound hi_fits
  have hn_bound : nodeBase + 12 * nodeIdx + nodeWords.length ≤ s₁.frontier := by
    change nodeBase + 12 * nodeIdx + 12 ≤ s₁.frontier
    rw [show s₁.frontier = s.frontier from hfr₁]
    lia
  have hn_fits : ∀ v ∈ nodeWords, Fits w v := by
    simp only [nodeWords, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, hk_fit, h0_fit, h1_fit, hi_fit, hn_fit]
  let s₂ := (Memory.spec 0).clientState s₁ p_nd
  obtain ⟨hv_nd, hm_nd, hfr₂, hs₂_mem, hs₂_hold⟩ :=
    writeRecord_spec w (nodeBase + 12 * nodeIdx) nodeWords s₁ hn_bound hn_fits
  have hs₂_nd (j : ℕ) (hj : j < 12) : s₂.mem (nodeBase + 12 * nodeIdx + j) =
      match j with
      | 0 => origKey | 1 => 0 | 2 => 1 | 3 => 1 | 4 => itemIdx | 5 => itemIdx
      | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | 10 => 0 | 11 => nodeIdx | _ => 0 := by
    have hget := hs₂_hold.get j hj
    interval_cases j <;> exact hget
  have hs₂_item (k : ℕ) (hk : k < 3) :
      s₂.mem (itemBase + 3 * itemIdx + k) = itWords[k]'hk := by
    refine Eq.trans ?_ (hs₁_hold.get k hk)
    by_contra hne
    rcases hs₂_mem _ hne with ⟨j, hj, heq⟩
    exact hdisj j hj k hk heq.symm
  have hs_eq : (Memory.spec 0).clientState s
      (shInsertInit ![itemBase, nodeBase, itemIdx, nodeIdx, val, origKey]) = s₂ := by
    rw [hsplit, StateTransitionSpec.clientState_bind]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsplit]
    exact validHistory_bind_step hv_it hv_nd
  · rw [hsplit, memoryCost_bind']
    exact congrArg₂ (· + ·) hm_it hm_nd
  · rw [hs_eq]; exact hfr₂.trans hfr₁
  · intro a ha
    rw [hs_eq] at ha
    by_cases h21 : s₂.mem a = s₁.mem a
    · rw [h21] at ha; exact Or.inl (hs₁_mem a ha)
    · exact Or.inr (hs₂_mem a h21)
  · rw [hs_eq]
    refine TreeMemRep.node (by dsimp; omega)
      (by simpa using hs₂_nd 0 (by decide))
      (by simpa using hs₂_nd 1 (by decide))
      (by simpa [targetSize] using hs₂_nd 2 (by decide))
      (by simpa using hs₂_nd 3 (by decide))
      ?_
      (by simpa using hs₂_nd 6 (by decide))
      (by simpa using hs₂_nd 7 (by decide))
      (fun _ h => by cases h) (fun _ h => by cases h)
    rw [hs₂_nd 4 (by decide), hs₂_nd 5 (by decide)]
    exact ⟨rfl, rfl, by dsimp; lia, hs₂_item 0 (by decide), hs₂_item 1 (by decide),
      hs₂_item 2 (by decide)⟩
  · rw [hs_eq]; exact hs₂_nd 8 (by decide)
  · rw [hs_eq]; exact hs₂_nd 9 (by decide)
  · rw [hs_eq]; exact hs₂_nd 10 (by decide)
  · rw [hs_eq]; exact hs₂_nd 11 (by decide)

private theorem combineWriteParent_spec {w nodeBase z y p rank target : ℕ} {s : Memory.State}
    (h16 : Fits w 16) (_hwf : Memory.WellFormed w s)
    (hp_lt : nodeBase + 12 * p + 11 < s.frontier)
    (hz_fit : Fits w z) (hy_fit : Fits w y) (hrk_fit : Fits w rank) (htg_fit : Fits w target) :
    let d : Fin 6 → ℕ := ![nodeBase, z, y, p, rank, target]
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (combineWriteParent d)) ∧
    memoryCost (combineWriteParent d) s = 12 ∧
    let s' := (Memory.spec 0).clientState s (combineWriteParent d)
    s'.frontier = s.frontier ∧
    (∀ a, s'.mem a ≠ s.mem a → ∃ j < 12, a = nodeBase + 12 * p + j) ∧
    (∀ j < 12, s'.mem (nodeBase + 12 * p + j) =
      match j with
      | 0 => 0 | 1 => rank | 2 => target | 3 => 0 | 4 => 0 | 5 => 0
      | 6 => z | 7 => y | 8 => 0 | 9 => 0 | 10 => 0 | 11 => 0 | _ => 0) := by
  have h0_fit : Fits w 0 := h16.of_le (by lia)
  let words := [0, rank, target, 0, 0, 0, z, y, 0, 0, 0, 0]
  have hp_eq : combineWriteParent ![nodeBase, z, y, p, rank, target] =
      Block.writeList (nodeBase + 12 * p) words := by
    dsimp only [combineWriteParent]
    simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    simp only [words, Block.writeList_cons, Block.writeList_nil, pure_unit_eq, bind_pure,
      Nat.add_assoc, Nat.reduceAdd]
  have hp_bound : nodeBase + 12 * p + words.length ≤ s.frontier := by
    change nodeBase + 12 * p + 12 ≤ s.frontier
    lia
  have hp_fits : ∀ v ∈ words, Fits w v := by
    simp only [words, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, h0_fit, hrk_fit, htg_fit, hz_fit, hy_fit]
  obtain ⟨hv, hm, hfr, hmod, hhold⟩ :=
    writeRecord_spec w (nodeBase + 12 * p) words s hp_bound hp_fits
  change _ ∧ _ ∧ _
  simp only [hp_eq]
  refine ⟨hv, hm, hfr, hmod, ?_⟩
  intro j hj
  have hget := hhold.get j hj
  interval_cases j <;> exact hget

private theorem combineInitParent_spec {rt w nodeBase z y p zRank : ℕ} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hp_lt : nodeBase + 12 * p + 11 < s.frontier)
    (hz_fit : Fits w z) (hy_fit : Fits w y)
    (hrk_fit : Fits w (zRank + 1)) (htg_fit : Fits w (targetSize rt (zRank + 1))) :
    let zTgt := targetSize rt zRank
    let d : Fin 7 → ℕ := ![nodeBase, z, y, p, zRank, zTgt, rt]
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (combineInitParent d)) ∧
    memoryCost (combineInitParent d) s = 12 ∧
    let s' := (Memory.spec 0).clientState s (combineInitParent d)
    s'.frontier = s.frontier ∧
    (∀ a, s'.mem a ≠ s.mem a → ∃ j < 12, a = nodeBase + 12 * p + j) ∧
    (∀ j < 12, s'.mem (nodeBase + 12 * p + j) =
      match j with
      | 0 => 0 | 1 => zRank + 1 | 2 => targetSize rt (zRank + 1) | 3 => 0 | 4 => 0 | 5 => 0
      | 6 => z | 7 => y | 8 => 0 | 9 => 0 | 10 => 0 | 11 => 0 | _ => 0) := by
  have hprog : combineInitParent ![nodeBase, z, y, p, zRank, targetSize rt zRank, rt] =
      combineWriteParent ![nodeBase, z, y, p, zRank + 1, targetSize rt (zRank + 1)] := by
    dsimp only [combineInitParent]
    simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    rw [targetSize_succ rt zRank]
    by_cases h1 : zRank + 1 ≤ rt
    · simp only [h1, ↓reduceIte]
    · by_cases h2 : (zRank + 1 - rt) % 2 = 1
      · simp only [h1, h2, ↓reduceIte]
      · simp only [h1, h2, ↓reduceIte]
  dsimp only
  rw [hprog]
  exact combineWriteParent_spec h16 hwf hp_lt hz_fit hy_fit hrk_fit htg_fit

private theorem combinePopFront_spec {w nodeBase : ℕ} {s : Memory.State}
    {y : SHTree} {rest : List SHTree}
    (h16 : Fits w 16)
    (hrep : RootListRep nodeBase s.mem 0 (y :: rest))
    (hpos : ∀ t ∈ y :: rest, 0 < t.rootId)
    (hlt : ∀ t ∈ y :: rest, nodeBase + 12 * t.rootId + 11 < s.frontier)
    (hnd : ((y :: rest).map SHTree.rootId).Nodup) :
    let d : Fin 2 → ℕ := ![nodeBase, y.rootId]
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (combinePopFront d)) ∧
    memoryCost (combinePopFront d) s ≤ 2 ∧
    (Memory.spec 0).clientResult s (combinePopFront d) = rest.head?.elim 0 SHTree.rootId ∧
    let s' := (Memory.spec 0).clientState s (combinePopFront d)
    s'.frontier = s.frontier ∧
    (∀ a, s'.mem a ≠ s.mem a →
      ∃ r0, rest.head? = some r0 ∧ a = nodeBase + 12 * r0.rootId + 9) ∧
    RootListRep nodeBase s'.mem 0 rest := by
  have hy_lt := hlt y (by simp)
  rcases hrep with ⟨_, _, hy_10, _, hrest_rep⟩
  cases rest with
  | nil =>
    have hn0 : ([] : List SHTree).head?.elim 0 SHTree.rootId = 0 := rfl
    rw [hn0] at hy_10
    have hv : (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (combinePopFront ![nodeBase, y.rootId])) := by
      dsimp only [combinePopFront]
      simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one]
      refine validHistory_read_bind (by omega) ?_
      simp only [hy_10, ne_eq, not_true_eq_false, ↓reduceIte]
      exact validHistory_pure w _ _
    have hm : memoryCost (combinePopFront ![nodeBase, y.rootId]) s ≤ 2 := by
      dsimp only [combinePopFront]
      simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read]
      simp only [hy_10, ne_eq, not_true_eq_false, ↓reduceIte, memoryCost_pure]
      decide
    have hres : (Memory.spec 0).clientResult s (combinePopFront ![nodeBase, y.rootId]) = 0 := by
      dsimp only [combinePopFront]
      simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [clientResult_bind_read]
      simp only [hy_10, ne_eq, not_true_eq_false, ↓reduceIte]
      rfl
    have hs' : (Memory.spec 0).clientState s (combinePopFront ![nodeBase, y.rootId]) = s := by
      dsimp only [combinePopFront]
      simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [clientState_bind_read]
      simp only [hy_10, ne_eq, not_true_eq_false, ↓reduceIte]
      rfl
    refine ⟨hv, hm, hres, ?_, ?_, ?_⟩
    · rw [hs']
    · intro a ha; rw [hs'] at ha; exact absurd rfl ha
    · rw [hs']; trivial
  | cons r0 rest' =>
    have hr0_pos : 0 < r0.rootId := hpos r0 (by simp)
    have hr0_ne0 : r0.rootId ≠ 0 := by omega
    have hr0_lt := hlt r0 (by simp)
    have hy_10' : s.mem (nodeBase + 12 * y.rootId + 10) = r0.rootId := by
      simpa using hy_10
    have h0_fit : Fits w 0 := h16.of_le (by omega)
    have hv : (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (combinePopFront ![nodeBase, y.rootId])) := by
      dsimp only [combinePopFront]
      simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one]
      refine validHistory_read_bind (by omega) ?_
      simp only [hy_10', hr0_ne0, ne_eq, not_false_eq_true, ↓reduceIte]
      exact validHistory_write_bind (by omega) h0_fit (validHistory_pure w _ _)
    have hm : memoryCost (combinePopFront ![nodeBase, y.rootId]) s ≤ 2 := by
      dsimp only [combinePopFront]
      simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read]
      simp only [hy_10', hr0_ne0, ne_eq, not_false_eq_true, ↓reduceIte,
        memoryCost_bind', memoryCost_write, memoryCost_pure]
      decide
    have hres : (Memory.spec 0).clientResult s (combinePopFront ![nodeBase, y.rootId]) =
        r0.rootId := by
      dsimp only [combinePopFront]
      simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [clientResult_bind_read]
      simp only [hy_10', hr0_ne0, ne_eq, not_false_eq_true, ↓reduceIte]
      rw [StateTransitionSpec.clientResult_bind, clientState_write]
      rfl
    have hs' : (Memory.spec 0).clientState s (combinePopFront ![nodeBase, y.rootId]) =
        ⟨Function.update s.mem (nodeBase + 12 * r0.rootId + 9) 0, s.frontier⟩ := by
      dsimp only [combinePopFront]
      simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [clientState_bind_read]
      simp only [hy_10', hr0_ne0, ne_eq, not_false_eq_true, ↓reduceIte]
      rw [clientState_bind_write, StateTransitionSpec.clientState_pure]
    have hrest' : RootListRep nodeBase
        (Function.update s.mem (nodeBase + 12 * r0.rootId + 9) 0) 0 (r0 :: rest') := by
      rcases hrest_rep with ⟨hr0_rk, _, hr0_10, hr0_11, htail⟩
      refine ⟨hr0_rk, Function.update_self _ _ _, ?_, ?_, ?_⟩
      · rw [Function.update_of_ne (by omega)]; exact hr0_10
      · rw [Function.update_of_ne (by omega)]; exact hr0_11
      · refine RootListRep.congr (fun t ht j hj => ?_) htail
        have hnd' : ((r0 :: rest').map SHTree.rootId).Nodup := by
          rw [List.map_cons, List.nodup_cons] at hnd; exact hnd.2
        rw [List.map_cons, List.nodup_cons] at hnd'
        have hne : t.rootId ≠ r0.rootId := fun heq => hnd'.1 (heq ▸ List.mem_map_of_mem ht)
        rcases hj with rfl | rfl | rfl <;> exact (Function.update_of_ne (by omega) _ _).symm
    refine ⟨hv, hm, ?_, ?_, ?_, ?_⟩
    · simpa using hres
    · rw [hs']
    · intro a ha
      rw [hs'] at ha
      by_cases ha9 : a = nodeBase + 12 * r0.rootId + 9
      · exact ⟨r0, rfl, ha9⟩
      · simp only [Function.update_of_ne ha9] at ha; exact absurd rfl ha
    · rw [hs']; exact hrest'

private theorem combinePreInit_spec {rt w itemBase nodeBase nc fuel : ℕ} {s : Memory.State}
    {z y : SHTree} {rest : List SHTree}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hz_mem : TreeMemRep rt itemBase nodeBase s.mem z)
    (hy_mem : TreeMemRep rt itemBase nodeBase s.mem y)
    (hz_val : z.Valid rt 0) (hy_val : y.Valid rt 0)
    (hrk_eq : y.rank = z.rank)
    (hrep : RootListRep nodeBase s.mem 0 (y :: rest))
    (hpos : ∀ t ∈ y :: rest, 0 < t.rootId)
    (hlt_roots : ∀ t ∈ y :: rest, nodeBase + 12 * t.rootId + 11 < s.frontier)
    (hnd_roots : ((y :: rest).map SHTree.rootId).Nodup)
    (hz_lt : ∀ id ∈ z.nodeIds, nodeBase + 12 * id + 11 < s.frontier)
    (hy_lt : ∀ id ∈ y.nodeIds, nodeBase + 12 * id + 11 < s.frontier)
    (hp_lt : nodeBase + 12 * (nc + 1) + 11 < s.frontier)
    (hp_fresh_z : nc + 1 ∉ z.nodeIds) (hp_fresh_y : nc + 1 ∉ y.nodeIds)
    (hp_fresh_rest : ∀ t ∈ rest, nc + 1 ∉ t.nodeIds)
    (_hp_fit : Fits w (nc + 1)) (hrk_fit : Fits w (z.rank + 1))
    (htg_fit : Fits w (targetSize rt (z.rank + 1)))
    (hdisj : ∀ nid, (nid = nc + 1 ∨ ∃ r0, rest.head? = some r0 ∧ nid = r0.rootId) →
      ∀ it ∈ z.allItems ++ y.allItems, ∀ j < 12, ∀ k < 3,
      nodeBase + 12 * nid + j ≠ itemBase + 3 * it.id + k) :
    let d : Fin 7 → ℕ := ![itemBase, nodeBase, z.rootId, y.rootId, nc, fuel, rt]
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (combinePreInit d)) ∧
    memoryCost (combinePreInit d) s ≤ 16 ∧
    (Memory.spec 0).clientResult s (combinePreInit d) = rest.head?.elim 0 SHTree.rootId ∧
    let s' := (Memory.spec 0).clientState s (combinePreInit d)
    s'.frontier = s.frontier ∧
    (∀ a, s'.mem a ≠ s.mem a →
      (∃ j < 12, a = nodeBase + 12 * (nc + 1) + j) ∨
      (∃ r0, rest.head? = some r0 ∧ a = nodeBase + 12 * r0.rootId + 9)) ∧
    let p : SHTree := .node (nc + 1) (z.rank + 1) 0 [] (some z) (some y)
    TreeMemRep rt itemBase nodeBase s'.mem p ∧
    ZipCurValid rt 0 p ∧
    RootListRep nodeBase s'.mem 0 rest ∧
    s'.mem (nodeBase + 12 * p.rootId + 8) = 0 := by
  have hz_rlt : nodeBase + 12 * z.rootId + 11 < s.frontier := hz_lt z.rootId z.rootId_mem_nodeIds
  have hz_rk := hz_mem.rank_eq
  have hz_tgt := hz_mem.target_eq
  have hpop := combinePopFront_spec h16 hrep hpos hlt_roots hnd_roots
  rcases hpop with ⟨hv_pop, hm_pop, hres_pop, hfr_pop, hmem_pop, hrest_pop⟩
  obtain ⟨s₁, hs₁_eq⟩ : ∃ s₁, s₁ = (Memory.spec 0).clientState s
      (combinePopFront ![nodeBase, y.rootId]) := ⟨_, rfl⟩
  rw [← hs₁_eq] at hfr_pop hmem_pop hrest_pop
  have hwf₁ : Memory.WellFormed w s₁ := by
    rw [hs₁_eq]; exact wellFormed_clientState hwf hv_pop
  have hz_fit : Fits w z.rootId := hwf₁.fits_of_lt_frontier (by omega)
  have hy_lt0 := hy_lt y.rootId y.rootId_mem_nodeIds
  have hy_fit : Fits w y.rootId := hwf₁.fits_of_lt_frontier (by omega)
  have hinit := combineInitParent_spec h16 hwf₁ (by rw [hfr_pop]; exact hp_lt)
    hz_fit hy_fit hrk_fit htg_fit
  rcases hinit with ⟨hv_in, hm_in, hfr_in, hmem_in, hs2_fields⟩
  obtain ⟨s₂, hs₂_eq⟩ : ∃ s₂, s₂ = (Memory.spec 0).clientState s₁
      (combineInitParent
        ![nodeBase, z.rootId, y.rootId, nc + 1, z.rank, targetSize rt z.rank, rt]) :=
    ⟨_, rfl⟩
  rw [← hs₂_eq] at hfr_in hmem_in hs2_fields
  have hv : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (combinePreInit ![itemBase, nodeBase, z.rootId, y.rootId, nc, fuel, rt])) := by
    dsimp only [combinePreInit]
    simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    refine validHistory_read_bind (by omega) (validHistory_read_bind (by omega) ?_)
    refine validHistory_bind_step hv_pop ?_
    rw [hz_rk, hz_tgt, ← hs₁_eq]
    refine validHistory_bind_step hv_in ?_
    exact validHistory_pure w _ _
  have hm : memoryCost (combinePreInit ![itemBase, nodeBase, z.rootId, y.rootId, nc, fuel, rt]) s ≤
      16 := by
    dsimp only [combinePreInit]
    simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    repeat (rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read])
    rw [memoryCost_bind', hz_rk, hz_tgt, ← hs₁_eq, memoryCost_bind', memoryCost_pure, add_zero]
    omega
  have hres : (Memory.spec 0).clientResult s
      (combinePreInit ![itemBase, nodeBase, z.rootId, y.rootId, nc, fuel, rt]) =
      rest.head?.elim 0 SHTree.rootId := by
    dsimp only [combinePreInit]
    simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    repeat rw [clientResult_bind_read]
    rw [StateTransitionSpec.clientResult_bind, hz_rk, hz_tgt, ← hs₁_eq]
    rw [StateTransitionSpec.clientResult_bind, hres_pop]
    rfl
  have hs_eq : (Memory.spec 0).clientState s
      (combinePreInit ![itemBase, nodeBase, z.rootId, y.rootId, nc, fuel, rt]) = s₂ := by
    dsimp only [combinePreInit]
    simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    repeat rw [clientState_bind_read]
    rw [StateTransitionSpec.clientState_bind, hz_rk, hz_tgt, ← hs₁_eq]
    rw [StateTransitionSpec.clientState_bind, ← hs₂_eq]
    rfl
  have hframe : ∀ a, s₂.mem a ≠ s.mem a →
      (∃ j < 12, a = nodeBase + 12 * (nc + 1) + j) ∨
      (∃ r0, rest.head? = some r0 ∧ a = nodeBase + 12 * r0.rootId + 9) := by
    intro a ha
    by_cases h21 : s₂.mem a = s₁.mem a
    · rw [h21] at ha; exact Or.inr (hmem_pop a ha)
    · exact Or.inl (hmem_in a h21)
  have hagree_node : ∀ nid, nid ≠ nc + 1 → ∀ j < 8,
      s.mem (nodeBase + 12 * nid + j) = s₂.mem (nodeBase + 12 * nid + j) := by
    intro nid hne j hj
    symm
    by_contra hdiff
    rcases hframe _ hdiff with ⟨j', _, heq⟩ | ⟨r0, _, heq⟩ <;> omega
  have hagree_item : ∀ it ∈ z.allItems ++ y.allItems, ∀ k < 3,
      s.mem (itemBase + 3 * it.id + k) = s₂.mem (itemBase + 3 * it.id + k) := by
    intro it hit k hk
    symm
    by_contra hdiff
    rcases hframe _ hdiff with ⟨j, hj, heq⟩ | ⟨r0, hr0, heq⟩
    · exact hdisj (nc + 1) (Or.inl rfl) it hit j hj k hk heq.symm
    · exact hdisj r0.rootId (Or.inr ⟨r0, hr0, rfl⟩) it hit 9 (by decide) k hk heq.symm
  have hz_mem₂ : TreeMemRep rt itemBase nodeBase s₂.mem z :=
    TreeMemRep.congr (fun nid hnid => hagree_node nid (fun h => hp_fresh_z (h ▸ hnid)))
      (fun it hit => hagree_item it (List.mem_append_left _ hit)) hz_mem
  have hy_mem₂ : TreeMemRep rt itemBase nodeBase s₂.mem y :=
    TreeMemRep.congr (fun nid hnid => hagree_node nid (fun h => hp_fresh_y (h ▸ hnid)))
      (fun it hit => hagree_item it (List.mem_append_right _ hit)) hy_mem
  have hp_mem : TreeMemRep rt itemBase nodeBase s₂.mem
      (.node (nc + 1) (z.rank + 1) 0 [] (some z) (some y)) := by
    refine TreeMemRep.node (by omega)
      (by simpa using hs2_fields 0 (by decide))
      (by simpa using hs2_fields 1 (by decide))
      (by simpa using hs2_fields 2 (by decide))
      (by simpa using hs2_fields 3 (by decide))
      ⟨by simpa using hs2_fields 4 (by decide), by simpa using hs2_fields 5 (by decide)⟩
      (by simpa using hs2_fields 6 (by decide))
      (by simpa using hs2_fields 7 (by decide))
      (fun c hc => by cases hc; exact hz_mem₂)
      (fun c hc => by cases hc; exact hy_mem₂)
  have hp_val : ZipCurValid rt 0 (.node (nc + 1) (z.rank + 1) 0 [] (some z) (some y)) := by
    refine ⟨Nat.zero_le _, le_rfl, (fun _ h => by cases h), (fun _ _ h => by cases h),
      (fun _ => Or.inl rfl), (fun c hc => by cases hc; exact ⟨rfl, hz_val⟩),
      (fun c hc => by cases hc; exact ⟨by rw [hrk_eq]; rfl, hy_val⟩)⟩
  have hrest₂ : RootListRep nodeBase s₂.mem 0 rest := by
    refine RootListRep.congr (fun t ht j hj => ?_) hrest_pop
    have hne : t.rootId ≠ nc + 1 := fun h => hp_fresh_rest t ht (h ▸ t.rootId_mem_nodeIds)
    symm
    by_contra hdiff
    rcases hmem_in _ hdiff with ⟨j', hj', heq⟩
    rcases hj with rfl | rfl | rfl <;> omega
  refine ⟨hv, hm, hres, ?_, ?_, ?_, hp_val, ?_, ?_⟩
  · rw [hs_eq]; exact hfr_in.trans hfr_pop
  · intro a ha; rw [hs_eq] at ha; exact hframe a ha
  · rw [hs_eq]; exact hp_mem
  · rw [hs_eq]; exact hrest₂
  · rw [hs_eq]; simpa [SHTree.rootId] using hs2_fields 8 (by decide)

private structure CombineInv (rt w ic₀ nc₀ maxItems maxNodes itemBase nodeBase : ℕ)
    (itemCount : ℕ) (origItems : List SHItem) (origEntries : List (SHItem × ℕ))
    (newIt : SHItem) (z : SHTree) (remRoots : List SHTree) (nc cont : ℕ)
    (created : ℕ → ℕ) (s : Memory.State) : Prop where
  fits16 : Fits w 16
  wf : Memory.WellFormed w s
  ic_le : ic₀ ≤ itemCount
  ic_lt : itemCount < maxItems
  nc_le : nc₀ ≤ nc
  nc_max : nc ≤ maxNodes
  pool_cap : nc₀ + 2 * (maxItems - ic₀) ≤ maxNodes
  nc_roots_le : (nc - nc₀) + (1 + remRoots.length) ≤ 2 * (itemCount + 1 - ic₀)
  item_pool_lt : itemBase + 3 * (maxItems + 1) ≤ s.frontier
  node_pool_lt : nodeBase + 12 * (maxNodes + 1) ≤ s.frontier
  pools_disj : itemBase + 3 * (maxItems + 1) ≤ nodeBase ∨
    nodeBase + 12 * (maxNodes + 1) ≤ itemBase
  fits_fuel : Fits w (shFuelBound rt maxItems)
  z_valid : z.Valid rt 0
  z_pop : popDeficit rt z = 0
  z_mem : TreeMemRep rt itemBase nodeBase s.mem z
  rem_valid : ∀ t ∈ remRoots, t.Valid rt 0
  rem_mem : ∀ t ∈ remRoots, TreeMemRep rt itemBase nodeBase s.mem t
  rem_rootList : RootListRep nodeBase s.mem 0 remRoots
  rem_rk_ge : ∀ u ∈ remRoots, z.rank ≤ u.rank
  cont_zero_lt : cont = 0 → ∀ u ∈ remRoots, z.rank < u.rank
  nodeIds_nodup : (forestNodeIds (z :: remRoots)).Nodup
  nodeIds_range : ∀ id ∈ forestNodeIds (z :: remRoots), nc₀ < id ∧ id ≤ nc
  itemIds_nodup : (forestItemIds (z :: remRoots)).Nodup
  itemIds_range : ∀ id ∈ forestItemIds (z :: remRoots), ic₀ < id ∧ id ≤ itemCount + 1
  dead_nodes_empty : ∀ idx, nc₀ < idx → idx ≤ nc →
    idx ∉ forestNodeIds (z :: remRoots) → s.mem (nodeBase + 12 * idx + 4) = 0
  created_zero : created 0 = itemCount + 1 - ic₀
  created_step : ∀ k, 2 * created (k + 1) +
    (z :: remRoots).countP (fun t => decide (t.rank = k)) ≤ created k
  live_rank_le : ∀ k, ((z :: remRoots).map (SHTree.countRank k)).sum ≤ created k
  rank_le : ∀ t ∈ z :: remRoots, t.rank ≤ nc - nc₀
  items_perm : (forestItems (z :: remRoots)).Perm (newIt :: origItems)
  entries_mono : ∀ p ∈ forestEntries (z :: remRoots),
    (p.1 = newIt ∧ newIt.origKey ≤ p.2) ∨
    ∃ c₀, (p.1, c₀) ∈ origEntries ∧ c₀ ≤ p.2

private theorem combineOne_spec {rt w ic₀ nc₀ maxItems maxNodes itemBase nodeBase : ℕ}
    {itemCount : ℕ} {origItems : List SHItem} {origEntries : List (SHItem × ℕ)}
    {newIt : SHItem} {z y : SHTree} {rest : List SHTree} {nc cont fuel : ℕ}
    {created : ℕ → ℕ} {s : Memory.State}
    (hinv : CombineInv rt w ic₀ nc₀ maxItems maxNodes itemBase nodeBase itemCount origItems
      origEntries newIt z (y :: rest) nc cont created s)
    (hrk_eq : y.rank = z.rank)
    (hfuel_ge : shFuelBound rt maxItems ≤ fuel) (hf_fit : Fits w fuel) :
    let d : Fin 7 → ℕ := ![itemBase, nodeBase, z.rootId, y.rootId, nc, fuel, rt]
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (combineOne d)) ∧
    combineOneSafe w d s ∧
    (Memory.spec 0).clientResult s (combineOne d) =
      (nc + 1, rest.head?.elim 0 SHTree.rootId) ∧
    let s' := (Memory.spec 0).clientState s (combineOne d)
    s'.frontier = s.frontier ∧
    (∀ a, s'.mem a ≠ s.mem a → InPoolRaw ic₀ nc₀ maxItems maxNodes itemBase nodeBase a) ∧
    ∃ z' created',
      z'.rootId = nc + 1 ∧
      z'.rank = z.rank + 1 ∧
      CombineInv rt w ic₀ nc₀ maxItems maxNodes itemBase nodeBase itemCount origItems origEntries
        newIt z' rest (nc + 1) 1 created' s' ∧
      (memoryCost (combineOne d) s : ℚ) + z'.phi rt ≤ z.phi rt + y.phi rt + 52 := by
  have h16 := hinv.fits16
  have hwf := hinv.wf
  have hnc_succ_sub : (nc + 1 - nc₀) + (1 + rest.length) ≤ 2 * (itemCount + 1 - ic₀) := by
    have := hinv.nc_roots_le; simp only [List.length_cons] at this; omega
  have hnc_succ_cap : nc + 1 ≤ nc₀ + 2 * (maxItems - ic₀) := by
    have := hinv.ic_lt; omega
  have hnc_succ_max : nc + 1 ≤ maxNodes := by have := hinv.pool_cap; omega
  have hnd_yr : (forestNodeIds (y :: rest)).Nodup :=
    (list_nodup_append_disj hinv.nodeIds_nodup).2.1
  have hp_lt : nodeBase + 12 * (nc + 1) + 11 < s.frontier := by
    have := hinv.node_pool_lt; omega
  have hp_fit : Fits w (nc + 1) := hwf.fits_of_lt_frontier (by omega)
  let created' : ℕ → ℕ := fun k => if k = z.rank + 1 then created (z.rank + 1) + 1 else created k
  have hcr'_zero : created' 0 = itemCount + 1 - ic₀ := by
    dsimp only [created']
    simp only [show (0 : ℕ) ≠ z.rank + 1 by omega, ↓reduceIte]
    exact hinv.created_zero
  have hcr_step' : ∀ k, 2 * created' (k + 1) +
      rest.countP (fun t => decide (t.rank = k)) +
      (if z.rank + 1 = k then 1 else 0) ≤ created' k := by
    intro k
    have hbase := hinv.created_step k
    have hcnt : (z :: y :: rest).countP (fun t => decide (t.rank = k)) =
        (if z.rank = k then 1 else 0) + (if y.rank = k then 1 else 0) +
          rest.countP (fun t => decide (t.rank = k)) := by
      simp [List.countP_cons]; omega
    rw [hcnt, hrk_eq] at hbase
    dsimp only [created']
    by_cases hk1 : k = z.rank
    · subst hk1
      simp only [↓reduceIte, show ¬ (z.rank = z.rank + 1) by omega,
        show ¬ (z.rank + 1 = z.rank) by omega] at hbase ⊢
      omega
    · by_cases hk2 : k = z.rank + 1
      · subst hk2
        simp only [↓reduceIte, show ¬ (z.rank + 1 + 1 = z.rank + 1) by omega,
          show ¬ (z.rank = z.rank + 1) by omega] at hbase ⊢
        omega
      · simp only [show ¬ (k + 1 = z.rank + 1) by omega, show ¬ (k = z.rank + 1) by omega,
          show ¬ (z.rank + 1 = k) by omega, show ¬ (z.rank = k) by omega, ↓reduceIte]
          at hbase ⊢
        omega
  have hcr'_decay : ∀ k, 2 * created' (k + 1) ≤ created' k := by
    intro k; have := hcr_step' k; omega
  have hpow_le : 2 ^ (z.rank + 1) ≤ maxItems := by
    have hm := Nat.pow_mul_le_of_step hcr'_decay (z.rank + 1)
    have hcpos : 1 ≤ created' (z.rank + 1) := by dsimp only [created']; simp
    have h1 : 2 ^ (z.rank + 1) ≤ 2 ^ (z.rank + 1) * created' (z.rank + 1) :=
      Nat.le_mul_of_pos_right _ hcpos
    rw [hcr'_zero] at hm
    have := hinv.ic_le
    have := hinv.ic_lt
    omega
  have hm_le_fuel : maxItems + 1 ≤ shFuelBound rt maxItems :=
    Nat.le_mul_of_pos_left (maxItems + 1) (by omega)
  have hrk_fit : Fits w (z.rank + 1) :=
    hinv.fits_fuel.of_le (by have := Nat.lt_two_pow_self (n := z.rank + 1); omega)
  have htg_fit : Fits w (targetSize rt (z.rank + 1)) :=
    hinv.fits_fuel.of_le (by have := targetSize_le_two_pow rt (z.rank + 1); omega)
  have hp_fresh_z : nc + 1 ∉ z.nodeIds := fun h => by
    have := (hinv.nodeIds_range _ (mem_forestNodeIds (by simp) h)).2; omega
  have hp_fresh_y : nc + 1 ∉ y.nodeIds := fun h => by
    have := (hinv.nodeIds_range _ (mem_forestNodeIds (by simp) h)).2; omega
  have hp_fresh_rest : ∀ t ∈ rest, nc + 1 ∉ t.nodeIds := fun t ht h => by
    have := (hinv.nodeIds_range _ (mem_forestNodeIds (by simp [ht]) h)).2; omega
  have hpos_yr : ∀ t ∈ y :: rest, 0 < t.rootId := fun t ht => by
    have := (hinv.nodeIds_range t.rootId (mem_forestNodeIds (by simp [ht])
      t.rootId_mem_nodeIds)).1
    omega
  have hlt_yr : ∀ t ∈ y :: rest, nodeBase + 12 * t.rootId + 11 < s.frontier := fun t ht => by
    have hle := (hinv.nodeIds_range t.rootId (mem_forestNodeIds (by simp [ht])
      t.rootId_mem_nodeIds)).2
    have := hinv.node_pool_lt
    omega
  have hnd_roots : ((y :: rest).map SHTree.rootId).Nodup := by
    have hsub : ((y :: rest).map SHTree.rootId).Sublist (forestNodeIds (y :: rest)) := by
      simp only [forestNodeIds]
      induction (y :: rest) with
      | nil => simp
      | cons a l ih =>
        simp only [List.map_cons, List.flatMap_cons]
        cases a with
        | node id _ _ _ left right =>
          rw [SHTree.nodeIds_node, SHTree.rootId]
          exact List.Sublist.cons_cons id (List.Sublist.trans ih (List.sublist_append_right _ _))
    exact hsub.nodup hnd_yr
  have hz_lt : ∀ id ∈ z.nodeIds, nodeBase + 12 * id + 11 < s.frontier := fun id hid => by
    have := (hinv.nodeIds_range id (mem_forestNodeIds (by simp) hid)).2
    have := hinv.node_pool_lt; omega
  have hy_lt : ∀ id ∈ y.nodeIds, nodeBase + 12 * id + 11 < s.frontier := fun id hid => by
    have := (hinv.nodeIds_range id (mem_forestNodeIds (by simp) hid)).2
    have := hinv.node_pool_lt; omega
  have hdisj_pre : ∀ nid, (nid = nc + 1 ∨ ∃ r0, rest.head? = some r0 ∧ nid = r0.rootId) →
      ∀ it ∈ z.allItems ++ y.allItems, ∀ j < 12, ∀ k < 3,
      nodeBase + 12 * nid + j ≠ itemBase + 3 * it.id + k := by
    intro nid hnid it hit j hj k hk
    have hnid_le : nid ≤ maxNodes := by
      rcases hnid with rfl | ⟨r0, hr0, rfl⟩
      · exact hnc_succ_max
      · have hr0_mem : r0 ∈ rest := by cases rest <;> simp_all
        have := (hinv.nodeIds_range r0.rootId (mem_forestNodeIds (by simp [hr0_mem])
          r0.rootId_mem_nodeIds)).2
        have := hinv.nc_max; omega
    have hiid_le : it.id ≤ maxItems := by
      have hit_f : it.id ∈ forestItemIds (z :: y :: rest) := by
        rcases List.mem_append.mp hit with h1 | h2
        · exact mem_forestItemIds (by simp) h1
        · exact mem_forestItemIds (by simp) h2
      have := (hinv.itemIds_range it.id hit_f).2
      have := hinv.ic_lt; omega
    rcases hinv.pools_disj with hd | hd <;> omega
  have hpre := combinePreInit_spec (fuel := fuel) h16 hwf hinv.z_mem (hinv.rem_mem y (by simp))
    hinv.z_valid (hinv.rem_valid y (by simp)) hrk_eq hinv.rem_rootList hpos_yr hlt_yr hnd_roots
    hz_lt hy_lt hp_lt hp_fresh_z hp_fresh_y hp_fresh_rest hp_fit hrk_fit htg_fit hdisj_pre
  rcases hpre with ⟨hv_pre, hm_pre, hres_pre, hfr_pre, hmem_pre, hp_mem, hp_val, hrest_pre, _⟩
  obtain ⟨s₁, hs₁_eq⟩ : ∃ s₁, s₁ = (Memory.spec 0).clientState s
      (combinePreInit ![itemBase, nodeBase, z.rootId, y.rootId, nc, fuel, rt]) := ⟨_, rfl⟩
  rw [← hs₁_eq] at hfr_pre hmem_pre hp_mem hrest_pre
  have hwf₁ : Memory.WellFormed w s₁ := by
    rw [hs₁_eq]; exact wellFormed_clientState hwf hv_pre
  let p : SHTree := .node (nc + 1) (z.rank + 1) 0 [] (some z) (some y)
  have hp_nd : p.nodeIds.Nodup := by
    rw [SHTree.nodeIds_node, Option.elim_some, Option.elim_some, List.cons_append, List.nodup_cons]
    have hzy_nd : (z.nodeIds ++ y.nodeIds).Nodup := by
      have := hinv.nodeIds_nodup
      simp only [forestNodeIds, List.flatMap_cons, ← List.append_assoc] at this
      exact (list_nodup_append_disj this).1
    exact ⟨fun h => by rcases List.mem_append.mp h with hz | hy <;>
      first | exact hp_fresh_z hz | exact hp_fresh_y hy, hzy_nd⟩
  have hp_id_nd : p.itemIds.Nodup := by
    rw [SHTree.itemIds_node, Option.elim_some, Option.elim_some, List.map_nil, List.nil_append]
    have := hinv.itemIds_nodup
    simp only [forestItemIds, List.flatMap_cons, ← List.append_assoc] at this
    exact (list_nodup_append_disj this).1
  have hp_id_rng : ∀ id ∈ p.itemIds, ic₀ < id ∧ id ≤ maxItems := by
    intro id hid
    have hmem_f : id ∈ forestItemIds (z :: y :: rest) := by
      rw [SHTree.itemIds_node, Option.elim_some, Option.elim_some, List.map_nil, List.nil_append]
        at hid
      simp only [forestItemIds, List.flatMap_cons, List.mem_append]
      rcases List.mem_append.mp hid with h1 | h2
      · exact Or.inl h1
      · exact Or.inr (Or.inl h2)
    have := hinv.itemIds_range id hmem_f
    have := hinv.ic_lt; omega
  have hp_nd_rng : ∀ id ∈ p.nodeIds, nc₀ < id ∧ id ≤ nc₀ + 2 * (maxItems - ic₀) := by
    intro id hid
    rw [SHTree.nodeIds_node, Option.elim_some, Option.elim_some, List.cons_append,
      List.mem_cons, List.mem_append] at hid
    rcases hid with rfl | (hz | hy)
    · have := hinv.nc_le; omega
    · have := hinv.nodeIds_range id (by simp [forestNodeIds, hz]); omega
    · have := hinv.nodeIds_range id (by simp [forestNodeIds, hy]); omega
  have hp_lt_1 : ∀ id ∈ p.nodeIds, nodeBase + 12 * id + 11 < s₁.frontier := by
    intro id hid
    have h1 := (hp_nd_rng id hid).2
    have h2 := hinv.pool_cap
    have h3 := hinv.node_pool_lt
    rw [hfr_pre]; omega
  have hp_it_lt_1 : ∀ it ∈ p.allItems, itemBase + 3 * it.id + 2 < s₁.frontier := by
    intro it hit
    have hid_in : it.id ∈ p.itemIds := List.mem_map_of_mem hit
    have := (hp_id_rng it.id hid_in).2
    have := hinv.item_pool_lt
    rw [hfr_pre]; omega
  have hdisj_p : ∀ id ∈ p.nodeIds, ∀ it ∈ p.allItems, ∀ j < 12, ∀ k < 3,
      nodeBase + 12 * id + j ≠ itemBase + 3 * it.id + k := by
    intro id hid it hit j hj k hk
    have h1 := (hp_nd_rng id hid).2
    have h2 := hinv.pool_cap
    have h3 := (hp_id_rng it.id (List.mem_map_of_mem hit)).2
    rcases hinv.pools_disj with hd | hd <;> omega
  have hp_fuel : p.phi rt + 5 ≤ 5 * (fuel : ℚ) := by
    have hle := tree_phi_le_fuel (rt := rt) hp_id_nd hp_id_rng hp_nd hp_nd_rng
    have hfq : ((shFuelBound rt maxItems : ℕ) : ℚ) ≤ (fuel : ℚ) := by exact_mod_cast hfuel_ge
    linarith
  have hdef := defill_spec h16 hwf₁ hp_val hp_nd hp_id_nd hp_mem hp_lt_1 hp_it_lt_1 hdisj_p
    hf_fit hp_fuel
  rcases hdef with ⟨hv_def, hsafe_def, hfr_def, hmem_def, z', hz'_root, hz'_rk, hz'_val,
    hz'_pop, _, hz'_nd, hz'_sub, hz'_dead, hz'_crk, hz'_perm, hz'_ck_mono, hz'_mem, hz'_phi⟩
  have hp_rt : p.rootId = nc + 1 := rfl
  have hp_rk : p.rank = z.rank + 1 := rfl
  rw [hp_rt] at hv_def hsafe_def hfr_def hmem_def hz'_root hz'_dead hz'_mem hz'_phi
  rw [hp_rk] at hz'_rk
  obtain ⟨s₂, hs₂_eq⟩ : ∃ s₂, s₂ = (Memory.spec 0).clientState s₁
      (defill ![itemBase, nodeBase, nc + 1, fuel]) := ⟨_, rfl⟩
  rw [← hs₂_eq] at hfr_def hmem_def hz'_dead hz'_mem
  have hwf₂ : Memory.WellFormed w s₂ := by
    rw [hs₂_eq]; exact wellFormed_clientState hwf₁ hv_def
  have hv : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s
        (combineOne ![itemBase, nodeBase, z.rootId, y.rootId, nc, fuel, rt])) := by
    dsimp only [combineOne]
    refine validHistory_bind_step hv_pre ?_
    simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    rw [← hs₁_eq]
    refine validHistory_bind_step hv_def ?_
    exact validHistory_pure w _ _
  have hsafe : combineOneSafe w ![itemBase, nodeBase, z.rootId, y.rootId, nc, fuel, rt] s := by
    have hrt_le_fb : rt ≤ shFuelBound rt maxItems :=
      Nat.le_trans (by omega : rt ≤ 50 * rt + 100)
        (Nat.le_mul_of_pos_right _ (Nat.succ_pos maxItems))
    have hrt_fit : Fits w rt := hinv.fits_fuel.of_le hrt_le_fb
    dsimp only [combineOneSafe]
    simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    rw [← hs₁_eq]
    exact ⟨h16, hp_fit, hrt_fit, hsafe_def⟩
  have hres : (Memory.spec 0).clientResult s
      (combineOne ![itemBase, nodeBase, z.rootId, y.rootId, nc, fuel, rt]) =
      (nc + 1, rest.head?.elim 0 SHTree.rootId) := by
    dsimp only [combineOne]
    simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    rw [StateTransitionSpec.clientResult_bind, ← hs₁_eq, hres_pre]
    rw [StateTransitionSpec.clientResult_bind]
    rfl
  have hs_eq : (Memory.spec 0).clientState s
      (combineOne ![itemBase, nodeBase, z.rootId, y.rootId, nc, fuel, rt]) = s₂ := by
    dsimp only [combineOne]
    simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    rw [StateTransitionSpec.clientState_bind, ← hs₁_eq]
    rw [StateTransitionSpec.clientState_bind, ← hs₂_eq]
    rfl
  have hm : memoryCost (combineOne ![itemBase, nodeBase, z.rootId, y.rootId, nc, fuel, rt]) s =
      memoryCost (combinePreInit ![itemBase, nodeBase, z.rootId, y.rootId, nc, fuel, rt]) s +
      memoryCost (defill ![itemBase, nodeBase, nc + 1, fuel]) s₁ := by
    dsimp only [combineOne]
    simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    rw [memoryCost_bind', ← hs₁_eq, memoryCost_bind', memoryCost_pure, add_zero]
  have hframe : ∀ a, s₂.mem a ≠ s.mem a →
      InPoolRaw ic₀ nc₀ maxItems maxNodes itemBase nodeBase a := by
    intro a ha
    by_cases h21 : s₂.mem a = s₁.mem a
    · rw [h21] at ha
      rcases hmem_pre a ha with ⟨j, hj, rfl⟩ | ⟨r0, hr0, rfl⟩
      · right; have := hinv.nc_le; omega
      · right
        have hr0_mem : r0 ∈ rest := by
          cases rest with | nil => cases hr0 | cons a as => cases hr0; exact List.mem_cons_self
        have := hinv.nodeIds_range r0.rootId
          (mem_forestNodeIds (List.mem_cons_of_mem z (List.mem_cons_of_mem y hr0_mem))
            r0.rootId_mem_nodeIds)
        omega
    · rcases hmem_def a h21 with ⟨id, hid, j, hj, rfl⟩ | ⟨it, hit, rfl⟩
      · right; have := hp_nd_rng id hid; have := hinv.pool_cap; omega
      · left; have := hp_id_rng it.id (List.mem_map_of_mem hit); omega
  have hframe_rest_node : ∀ t ∈ rest, ∀ id ∈ t.nodeIds, ∀ j < 12,
      s₂.mem (nodeBase + 12 * id + j) = s₁.mem (nodeBase + 12 * id + j) := by
    intro t ht id hid j hj
    by_contra hdiff
    rcases hmem_def _ hdiff with ⟨idp, hidp, j', hj', heq⟩ | ⟨it, hit, heq⟩
    · have hne : id ≠ idp := by
        have hdisj_nr : ∀ x ∈ p.nodeIds, x ∉ forestNodeIds rest := by
          intro x hx hxr
          rw [SHTree.nodeIds_node, Option.elim_some, Option.elim_some, List.cons_append,
            List.mem_cons, List.mem_append] at hx
          rcases hx with rfl | (hz | hy)
          · rcases List.mem_flatMap.mp hxr with ⟨u, hu, hu_in⟩
            exact hp_fresh_rest u hu hu_in
          · have hd := hinv.nodeIds_nodup
            simp only [forestNodeIds, List.flatMap_cons, ← List.append_assoc] at hd
            exact (list_nodup_append_disj hd).2.2 x (List.mem_append_left _ hz) hxr
          · have hd := hinv.nodeIds_nodup
            simp only [forestNodeIds, List.flatMap_cons, ← List.append_assoc] at hd
            exact (list_nodup_append_disj hd).2.2 x (List.mem_append_right _ hy) hxr
        exact fun h => hdisj_nr idp hidp (h ▸ mem_forestNodeIds ht hid)
      omega
    · have hid_le : id ≤ maxNodes := by
        have := (hinv.nodeIds_range id (mem_forestNodeIds
          (List.mem_cons_of_mem z (List.mem_cons_of_mem y ht)) hid)).2
        omega
      have hit_le : it.id ≤ maxItems := (hp_id_rng it.id (List.mem_map_of_mem hit)).2
      rcases hinv.pools_disj with hd | hd <;> omega
  have hframe_rest_item : ∀ t ∈ rest, ∀ it ∈ t.allItems, ∀ k < 3,
      s₂.mem (itemBase + 3 * it.id + k) = s₁.mem (itemBase + 3 * it.id + k) := by
    intro t ht it hit k hk
    by_contra hdiff
    rcases hmem_def _ hdiff with ⟨idp, hidp, j, hj, heq⟩ | ⟨itp, hitp, heq⟩
    · have hidp_le : idp ≤ maxNodes := by
        have := (hp_nd_rng idp hidp).2; have := hinv.pool_cap; omega
      have hit_le : it.id ≤ maxItems := by
        have := (hinv.itemIds_range it.id (mem_forestItemIds (by simp [ht]) hit)).2
        have := hinv.ic_lt; omega
      rcases hinv.pools_disj with hd | hd <;> omega
    · have hne : it.id ≠ itp.id := by
        have hd := hinv.itemIds_nodup
        simp only [forestItemIds, List.flatMap_cons, ← List.append_assoc] at hd
        intro heqi
        have hdis := (list_nodup_append_disj hd).2.2 it.id
        apply hdis
        · have hitp_id : itp.id ∈ p.itemIds := List.mem_map_of_mem hitp
          rw [SHTree.itemIds_node, Option.elim_some, Option.elim_some, List.map_nil,
            List.nil_append] at hitp_id
          rw [heqi]; exact hitp_id
        · simp only [List.mem_flatMap]
          exact ⟨t, ht, List.mem_map_of_mem hit⟩
      omega
  have hrem_mem₂ : ∀ t ∈ rest, TreeMemRep rt itemBase nodeBase s₂.mem t := by
    intro t ht
    refine TreeMemRep.congr (mem₁ := s₁.mem)
      (fun id hid j hj => (hframe_rest_node t ht id hid j (by omega)).symm)
      (fun it hit k hk => (hframe_rest_item t ht it hit k hk).symm) ?_
    · refine TreeMemRep.congr (fun id hid j hj => ?_) (fun it hit k hk => ?_)
        (hinv.rem_mem t (by simp [ht]))
      · by_contra hdiff
        rcases hmem_pre _ (Ne.symm hdiff) with ⟨j', _, heq⟩ | ⟨r0, _, heq⟩
        · have : id = nc + 1 := by omega
          exact hp_fresh_rest t ht (this ▸ hid)
        · omega
      · by_contra hdiff
        have hit_le : it.id ≤ maxItems := by
          have := (hinv.itemIds_range it.id (mem_forestItemIds (by simp [ht]) hit)).2
          have := hinv.ic_lt; omega
        rcases hmem_pre _ (Ne.symm hdiff) with ⟨j, hj, heq⟩ | ⟨r0, hr0, heq⟩
        · rcases hinv.pools_disj with hd | hd <;> omega
        · have hr0_mem : r0 ∈ rest := by
            cases rest with | nil => cases hr0 | cons a as => cases hr0; exact List.mem_cons_self
          have := (hinv.nodeIds_range r0.rootId (mem_forestNodeIds (by simp [hr0_mem])
            r0.rootId_mem_nodeIds)).2
          have := hinv.nc_max
          rcases hinv.pools_disj with hd | hd <;> omega
  have hrem_rl₂ : RootListRep nodeBase s₂.mem 0 rest := by
    refine RootListRep.congr (fun t ht j hj => ?_) hrest_pre
    exact (hframe_rest_node t ht t.rootId t.rootId_mem_nodeIds j (by
      rcases hj with rfl | rfl | rfl <;> omega)).symm
  have hp_perm : p.allItems.Perm (z.allItems ++ y.allItems) := by
    simp [p, SHTree.allItems_node]
  have hnd₂_nodup : (forestNodeIds (z' :: rest)).Nodup := by
    simp only [forestNodeIds, List.flatMap_cons, List.nodup_append]
    have hd_all := hinv.nodeIds_nodup
    simp only [forestNodeIds, List.flatMap_cons, ← List.append_assoc] at hd_all
    refine ⟨hz'_nd, (list_nodup_append_disj hd_all).2.1, ?_⟩
    intro x hx y' hy' rfl
    have hxp := hz'_sub x hx
    rw [SHTree.nodeIds_node, Option.elim_some, Option.elim_some, List.cons_append, List.mem_cons,
      List.mem_append] at hxp
    rcases hxp with rfl | (hz | hy)
    · rcases List.mem_flatMap.mp hy' with ⟨t, ht, htid⟩
      exact hp_fresh_rest t ht htid
    · exact (list_nodup_append_disj hd_all).2.2 x (List.mem_append_left _ hz) hy'
    · exact (list_nodup_append_disj hd_all).2.2 x (List.mem_append_right _ hy) hy'
  have hid₂_nodup : (forestItemIds (z' :: rest)).Nodup := by
    simp only [forestItemIds, List.flatMap_cons, List.nodup_append]
    have hz'_id_perm : z'.itemIds.Perm p.itemIds := hz'_perm.map SHItem.id
    have hd_all := hinv.itemIds_nodup
    simp only [forestItemIds, List.flatMap_cons, ← List.append_assoc] at hd_all
    refine ⟨hz'_id_perm.nodup_iff.mpr hp_id_nd, (list_nodup_append_disj hd_all).2.1, ?_⟩
    intro x hx y' hy' rfl
    have hxp := hz'_id_perm.mem_iff.mp hx
    rw [SHTree.itemIds_node, Option.elim_some, Option.elim_some, List.map_nil, List.nil_append]
      at hxp
    exact (list_nodup_append_disj hd_all).2.2 x hxp hy'
  have hinv' : CombineInv rt w ic₀ nc₀ maxItems maxNodes itemBase nodeBase itemCount origItems
      origEntries newIt z' rest (nc + 1) 1 created' s₂ := by
    refine ⟨h16, hwf₂, hinv.ic_le, hinv.ic_lt, by have := hinv.nc_le; omega, hnc_succ_max,
      hinv.pool_cap, hnc_succ_sub, hfr_def ▸ hfr_pre ▸ hinv.item_pool_lt,
      hfr_def ▸ hfr_pre ▸ hinv.node_pool_lt, hinv.pools_disj, hinv.fits_fuel,
      hz'_val, hz'_pop, hz'_mem, fun t ht => hinv.rem_valid t (by simp [ht]),
      hrem_mem₂, hrem_rl₂, ?_, ?_, hnd₂_nodup, ?_, hid₂_nodup, ?_, ?_, hcr'_zero, ?_, ?_, ?_,
      ?_, ?_⟩
    · intro u hu
      have hy_lt_u : y.rank < u.rank := hinv.rem_rootList.1 u hu
      rw [hz'_rk]; omega
    · intro h; exact absurd h (by decide)
    · intro id hid
      simp only [forestNodeIds, List.flatMap_cons, List.mem_append] at hid
      rcases hid with h1 | h2
      · have h1p := hz'_sub id h1
        rw [SHTree.nodeIds_node, Option.elim_some, Option.elim_some, List.cons_append,
          List.mem_cons, List.mem_append] at h1p
        rcases h1p with rfl | (hz | hy)
        · have := hinv.nc_le; omega
        · have := hinv.nodeIds_range id (by simp [forestNodeIds, hz]); omega
        · have := hinv.nodeIds_range id (by simp [forestNodeIds, hy]); omega
      · have := hinv.nodeIds_range id (by simp [forestNodeIds, h2]); omega
    · intro id hid
      simp only [forestItemIds, List.flatMap_cons, List.mem_append] at hid
      rcases hid with h1 | h2
      · have h1p : id ∈ p.itemIds := (hz'_perm.map SHItem.id).mem_iff.mp h1
        rw [SHTree.itemIds_node, Option.elim_some, Option.elim_some, List.map_nil,
          List.nil_append, List.mem_append] at h1p
        rcases h1p with hz | hy
        · exact hinv.itemIds_range id (by simp [forestItemIds, hz])
        · exact hinv.itemIds_range id (by simp [forestItemIds, hy])
      · exact hinv.itemIds_range id (by simp [forestItemIds, h2])
    · intro idx h1 h2 hnot
      by_cases h_last : idx = nc + 1
      · subst h_last
        exact absurd (by simp [forestNodeIds, ← hz'_root, z'.rootId_mem_nodeIds]) hnot
      · by_cases h_in_p : idx ∈ p.nodeIds
        · have h_not_z' : idx ∉ z'.nodeIds :=
            fun h => hnot (by simp [forestNodeIds, h])
          exact hz'_dead idx h_in_p h_not_z'
        · have h_not_old : idx ∉ forestNodeIds (z :: y :: rest) := by
            intro h
            simp only [forestNodeIds, List.flatMap_cons, List.mem_append] at h
            rcases h with hz | (hy | hr)
            · exact h_in_p (by simp [p, SHTree.nodeIds_node, hz])
            · exact h_in_p (by simp [p, SHTree.nodeIds_node, hy])
            · exact hnot (by simp [forestNodeIds, hr])
          have hs0 := hinv.dead_nodes_empty idx h1 (by omega) h_not_old
          have h21 : s₂.mem (nodeBase + 12 * idx + 4) = s₁.mem (nodeBase + 12 * idx + 4) := by
            by_contra hdiff
            rcases hmem_def _ hdiff with ⟨idp, hidp, j, hj, heq⟩ | ⟨it, hit, heq⟩
            · have : idx = idp := by omega
              exact h_in_p (this ▸ hidp)
            · have := (hp_id_rng it.id (List.mem_map_of_mem hit)).2
              rcases hinv.pools_disj with hd | hd <;> omega
          have h10 : s₁.mem (nodeBase + 12 * idx + 4) = s.mem (nodeBase + 12 * idx + 4) := by
            by_contra hdiff
            rcases hmem_pre _ hdiff with ⟨j, hj, heq⟩ | ⟨r0, _, heq⟩ <;> omega
          rw [h21, h10, hs0]
    · intro k
      have hc := hcr_step' k
      rw [List.countP_cons, hz'_rk]
      by_cases heq : z.rank + 1 = k
      · simp only [heq, decide_true, ↓reduceIte] at hc ⊢; omega
      · simp only [heq, decide_false, Bool.false_eq_true, ↓reduceIte] at hc ⊢; omega
    · intro k
      simp only [List.map_cons, List.sum_cons]
      have hzk := hz'_crk k
      simp only [SHTree.countRank_node, Option.elim_some] at hzk
      have hold := hinv.live_rank_le k
      simp only [List.map_cons, List.sum_cons] at hold
      dsimp only [created']
      by_cases hkr : k = z.rank + 1
      · subst hkr
        simp only [↓reduceIte] at hzk ⊢
        omega
      · simp only [show ¬ (z.rank + 1 = k) by omega, ↓reduceIte, Nat.zero_add] at hzk ⊢
        simp only [show ¬ (k = z.rank + 1) by omega, ↓reduceIte]
        omega
    · intro t ht
      rcases List.mem_cons.mp ht with rfl | ht'
      · rw [hz'_rk]; have := hinv.nc_le; have := hinv.rank_le z (by simp); omega
      · have := hinv.rank_le t (by simp [ht']); omega
    · refine List.Perm.trans ?_ hinv.items_perm
      simp only [forestItems, forestEntries, List.flatMap_cons, List.map_append]
      have hz'_it : (z'.allEntries.map Prod.fst).Perm
          ((z.allEntries.map Prod.fst) ++ (y.allEntries.map Prod.fst)) := by
        change z'.allItems.Perm (z.allItems ++ y.allItems)
        exact hz'_perm.trans hp_perm
      rw [← List.append_assoc]
      exact hz'_it.append_right _
    · intro pe hpe
      simp only [forestEntries, List.flatMap_cons, List.mem_append] at hpe
      rcases hpe with h1 | h2
      · rcases hz'_ck_mono pe h1 with ⟨c₁, hc₁_in, hc₁_le⟩
        simp only [SHTree.allEntries_node, List.map_nil, Option.elim_some, List.nil_append,
          List.mem_append] at hc₁_in
        have hc₁_f : (pe.1, c₁) ∈ forestEntries (z :: y :: rest) := by
          simp only [forestEntries, List.flatMap_cons, List.mem_append]
          rcases hc₁_in with hz | hy
          · exact Or.inl hz
          · exact Or.inr (Or.inl hy)
        rcases hinv.entries_mono (pe.1, c₁) hc₁_f with ⟨hne, hle⟩ | ⟨c₀, hc₀, hle⟩
        · exact Or.inl ⟨hne, le_trans hle hc₁_le⟩
        · exact Or.inr ⟨c₀, hc₀, le_trans hle hc₁_le⟩
      · exact hinv.entries_mono pe (by simp [forestEntries, h2])
  have hcost_phi : (memoryCost
        (combineOne ![itemBase, nodeBase, z.rootId, y.rootId, nc, fuel, rt]) s : ℚ) +
      z'.phi rt ≤ z.phi rt + y.phi rt + 52 := by
    have hm1 : (memoryCost (combinePreInit
        ![itemBase, nodeBase, z.rootId, y.rootId, nc, fuel, rt]) s : ℚ) ≤ 16 := by
      exact_mod_cast hm_pre
    have hz'_phi_p : (memoryCost (defill ![itemBase, nodeBase, nc + 1, fuel]) s₁ : ℚ) + z'.phi rt ≤
        p.phi rt + 6 := hz'_phi
    have hp_phi : p.phi rt = z.phi rt + y.phi rt + 30 := by
      simp [p, SHTree.phi, SHTree.itemPhiSum_node, SHTree.nodeCount_node]; ring
    rw [hm]
    push_cast
    linarith
  refine ⟨hv, hsafe, hres, ?_, ?_, z', created', hz'_root, hz'_rk, ?_, ?_⟩
  · rw [hs_eq]; exact hfr_def.trans hfr_pre
  · intro a ha; rw [hs_eq] at ha; exact hframe a ha
  · rw [hs_eq]; exact hinv'
  · exact hcost_phi

private theorem combineStep_spec {rt w ic₀ nc₀ maxItems maxNodes itemBase nodeBase : ℕ}
    {itemCount : ℕ} {origItems : List SHItem} {origEntries : List (SHItem × ℕ)}
    {newIt : SHItem} {z : SHTree} {remRoots : List SHTree} {nc cont fuel : ℕ}
    {created : ℕ → ℕ} {s : Memory.State}
    (hinv : CombineInv rt w ic₀ nc₀ maxItems maxNodes itemBase nodeBase itemCount origItems
      origEntries newIt z remRoots nc cont created s)
    (_hcont : cont ≠ 0)
    (hfuel_ge : shFuelBound rt maxItems ≤ fuel) (hf_fit : Fits w fuel) :
    let d : (ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ) :=
      ((itemBase, nodeBase, rt, fuel), (z.rootId, remRoots.head?.elim 0 SHTree.rootId, nc, cont))
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (combineStep d)) ∧
    combineStepSafe w d s ∧
    let res := (Memory.spec 0).clientResult s (combineStep d)
    let s' := (Memory.spec 0).clientState s (combineStep d)
    s'.frontier = s.frontier ∧
    (∀ a, s'.mem a ≠ s.mem a → InPoolRaw ic₀ nc₀ maxItems maxNodes itemBase nodeBase a) ∧
    ∃ z' remRoots' nc' cont' created',
      res = (z'.rootId, remRoots'.head?.elim 0 SHTree.rootId, nc', cont') ∧
      nc ≤ nc' ∧
      CombineInv rt w ic₀ nc₀ maxItems maxNodes itemBase nodeBase itemCount origItems origEntries
        newIt z' remRoots' nc' cont' created' s' ∧
      ((cont' = 1 ∧ remRoots'.length < remRoots.length ∧
        (memoryCost (combineStep d) s : ℚ) + totalPhi rt (z' :: remRoots') ≤
          totalPhi rt (z :: remRoots)) ∨
       (cont' = 0 ∧ z' = z ∧ remRoots' = remRoots ∧
         memoryCost (combineStep d) s ≤ 2 ∧ s' = s)) := by
  have h16 := hinv.fits16
  have hwf := hinv.wf
  have hz_lt : nodeBase + 12 * z.rootId + 11 < s.frontier := by
    have := (hinv.nodeIds_range z.rootId (mem_forestNodeIds (by simp) z.rootId_mem_nodeIds)).2
    have := hinv.nc_max; have := hinv.node_pool_lt; omega
  have hz_rk := hinv.z_mem.rank_eq
  cases remRoots with
  | nil =>
    have hn0 : ([] : List SHTree).head?.elim 0 SHTree.rootId = 0 := rfl
    simp only [hn0]
    have hv : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
        (combineStep ((itemBase, nodeBase, rt, fuel), (z.rootId, 0, nc, cont)))) := by
      dsimp only [combineStep, combineItemBase, combineNodeBase, combineRankThreshold,
          combineFuel,
      combineZ, combineFirstRoot, combineNodeCount]
      refine validHistory_read_bind (by omega) ?_
      simp only [↓reduceIte]
      exact validHistory_pure w _ _
    have hsafe : combineStepSafe w
        ((itemBase, nodeBase, rt, fuel), (z.rootId, 0, nc, cont)) s :=
      ⟨h16, fun h => absurd rfl h⟩
    have hm : memoryCost
        (combineStep ((itemBase, nodeBase, rt, fuel), (z.rootId, 0, nc, cont))) s ≤ 2 := by
      dsimp only [combineStep, combineItemBase, combineNodeBase, combineRankThreshold,
          combineFuel,
      combineZ, combineFirstRoot, combineNodeCount]
      rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read]
      simp only [↓reduceIte, memoryCost_pure]
      decide
    have hres : (Memory.spec 0).clientResult s
        (combineStep ((itemBase, nodeBase, rt, fuel), (z.rootId, 0, nc, cont))) =
        (z.rootId, 0, nc, 0) := by
      dsimp only [combineStep, combineItemBase, combineNodeBase, combineRankThreshold,
          combineFuel,
      combineZ, combineFirstRoot, combineNodeCount]
      rw [clientResult_bind_read]
      simp only [↓reduceIte]
      rfl
    have hs' : (Memory.spec 0).clientState s
        (combineStep ((itemBase, nodeBase, rt, fuel), (z.rootId, 0, nc, cont))) = s := by
      dsimp only [combineStep, combineItemBase, combineNodeBase, combineRankThreshold,
          combineFuel,
      combineZ, combineFirstRoot, combineNodeCount]
      rw [clientState_bind_read]
      simp only [↓reduceIte]
      rfl
    have hinv0 : CombineInv rt w ic₀ nc₀ maxItems maxNodes itemBase nodeBase itemCount origItems
        origEntries newIt z [] nc 0 created s :=
      { hinv with cont_zero_lt := fun _ u hu => by cases hu }
    refine ⟨hv, hsafe, ?_, ?_, z, [], nc, 0, created, ?_, le_rfl, ?_,
      Or.inr ⟨rfl, rfl, rfl, hm, hs'⟩⟩
    · simp [hs']
    · intro a ha; rw [hs'] at ha; exact absurd rfl ha
    · simp [hres]
    · simp [hs', hinv0]
  | cons y rest =>
    have hy_pos : 0 < y.rootId := by
      have := (hinv.nodeIds_range y.rootId (mem_forestNodeIds (by simp) y.rootId_mem_nodeIds)).1
      omega
    have hy_ne0 : y.rootId ≠ 0 := by omega
    have hy_lt : nodeBase + 12 * y.rootId + 11 < s.frontier := by
      have := (hinv.nodeIds_range y.rootId (mem_forestNodeIds (by simp) y.rootId_mem_nodeIds)).2
      have := hinv.nc_max; have := hinv.node_pool_lt; omega
    have hy_rk := (hinv.rem_mem y (by simp)).rank_eq
    have hy_ge_z : z.rank ≤ y.rank := hinv.rem_rk_ge y (by simp)
    have hhd : (y :: rest).head?.elim 0 SHTree.rootId = y.rootId := rfl
    by_cases hrk_eq : y.rank = z.rank
    · have hone := combineOne_spec hinv hrk_eq hfuel_ge hf_fit
      rcases hone with ⟨hv_one, hsafe_one, hres_one, hfr_one, hmem_one, z', created',
        hz'_rt, hz'_rk, hinv', hcost_one⟩
      obtain ⟨s', hs'_eq⟩ : ∃ s', s' = (Memory.spec 0).clientState s
          (combineOne ![itemBase, nodeBase, z.rootId, y.rootId, nc, fuel, rt]) := ⟨_, rfl⟩
      rw [← hs'_eq] at hfr_one hmem_one hinv'
      have hv : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
          (combineStep ((itemBase, nodeBase, rt, fuel), (z.rootId, y.rootId, nc, cont)))) := by
        dsimp only [combineStep, combineItemBase, combineNodeBase, combineRankThreshold,
          combineFuel, combineZ, combineFirstRoot, combineNodeCount]
        refine validHistory_read_bind (by omega) ?_
        simp only [hy_ne0, ↓reduceIte]
        refine validHistory_read_bind (by omega) ?_
        rw [hz_rk, hy_rk, hrk_eq]
        simp only [ne_eq, not_true_eq_false, ↓reduceIte]
        exact validHistory_bind_step hv_one (validHistory_pure w _ _)
      have hsafe : combineStepSafe w
          ((itemBase, nodeBase, rt, fuel), (z.rootId, y.rootId, nc, cont)) s := by
        refine ⟨h16, fun _ _ => hsafe_one⟩
      have hm : memoryCost
          (combineStep ((itemBase, nodeBase, rt, fuel), (z.rootId, y.rootId, nc, cont))) s =
          2 + memoryCost
            (combineOne ![itemBase, nodeBase, z.rootId, y.rootId, nc, fuel, rt]) s := by
        dsimp only [combineStep, combineItemBase, combineNodeBase, combineRankThreshold,
          combineFuel, combineZ, combineFirstRoot, combineNodeCount]
        rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read]
        simp only [hy_ne0, ↓reduceIte]
        rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
          hz_rk, hy_rk, hrk_eq]
        simp only [ne_eq, not_true_eq_false, ↓reduceIte, memoryCost_bind', memoryCost_pure,
          add_zero]
        omega
      have hres : (Memory.spec 0).clientResult s
          (combineStep ((itemBase, nodeBase, rt, fuel), (z.rootId, y.rootId, nc, cont))) =
          (nc + 1, rest.head?.elim 0 SHTree.rootId, nc + 1, 1) := by
        dsimp only [combineStep, combineItemBase, combineNodeBase, combineRankThreshold,
          combineFuel, combineZ, combineFirstRoot, combineNodeCount]
        rw [clientResult_bind_read]
        simp only [hy_ne0, ↓reduceIte]
        rw [clientResult_bind_read, hz_rk, hy_rk, hrk_eq]
        simp only [ne_eq, not_true_eq_false, ↓reduceIte]
        rw [StateTransitionSpec.clientResult_bind, hres_one]
        rfl
      have hs_eq : (Memory.spec 0).clientState s
          (combineStep ((itemBase, nodeBase, rt, fuel), (z.rootId, y.rootId, nc, cont))) = s' := by
        dsimp only [combineStep, combineItemBase, combineNodeBase, combineRankThreshold,
          combineFuel, combineZ, combineFirstRoot, combineNodeCount]
        rw [clientState_bind_read]
        simp only [hy_ne0, ↓reduceIte]
        rw [clientState_bind_read, hz_rk, hy_rk, hrk_eq]
        simp only [ne_eq, not_true_eq_false, ↓reduceIte]
        rw [StateTransitionSpec.clientState_bind, ← hs'_eq]
        rfl
      have hphi_drop : (memoryCost (combineStep
            ((itemBase, nodeBase, rt, fuel), (z.rootId, y.rootId, nc, cont))) s : ℚ) +
          totalPhi rt (z' :: rest) ≤ totalPhi rt (z :: y :: rest) := by
        rw [hm]
        simp only [totalPhi_cons rt, hz'_rk]
        have hpop_z : popDeficit rt z = 0 := hinv.z_pop
        have hpop_z' : popDeficit rt z' = 0 := hinv'.z_pop
        have hpop_y : 0 ≤ popDeficit rt y := popDeficit_nonneg rt y
        have hrc_z : rootCredit z.rank = 86 + 6 * (z.rank : ℚ) := rfl
        have hrc_y : rootCredit y.rank = 86 + 6 * (z.rank : ℚ) := by rw [hrk_eq]; rfl
        have hrc_z' : rootCredit (z.rank + 1) = 86 + 6 * ((z.rank + 1 : ℕ) : ℚ) := rfl
        have hrk_q : (0 : ℚ) ≤ (z.rank : ℚ) := Nat.cast_nonneg _
        rw [hpop_z, hpop_z', hrc_z, hrc_y, hrc_z']
        push_cast
        linarith
      refine ⟨hv, hsafe, ?_, ?_, z', rest, nc + 1, 1, created', ?_, by omega, ?_,
        Or.inl ⟨rfl, by simp, ?_⟩⟩
      · simpa [hhd, hs_eq] using hfr_one
      · intro a ha; simp only [hhd, hs_eq] at ha; exact hmem_one a ha
      · simpa [hhd, hz'_rt] using hres
      · simpa [hhd, hs_eq] using hinv'
      · simpa [hhd] using hphi_drop
    · have hv : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
          (combineStep ((itemBase, nodeBase, rt, fuel), (z.rootId, y.rootId, nc, cont)))) := by
        dsimp only [combineStep, combineItemBase, combineNodeBase, combineRankThreshold,
          combineFuel, combineZ, combineFirstRoot, combineNodeCount]
        refine validHistory_read_bind (by omega) ?_
        simp only [hy_ne0, ↓reduceIte]
        refine validHistory_read_bind (by omega) ?_
        rw [hz_rk, hy_rk]
        simp only [hrk_eq, ne_eq, not_false_eq_true, ↓reduceIte]
        exact validHistory_pure w _ _
      have hsafe : combineStepSafe w
          ((itemBase, nodeBase, rt, fuel), (z.rootId, y.rootId, nc, cont)) s := by
        refine ⟨h16, fun _ h => absurd (by rw [hz_rk, hy_rk] at h; exact h) hrk_eq⟩
      have hm : memoryCost
          (combineStep ((itemBase, nodeBase, rt, fuel), (z.rootId, y.rootId, nc, cont))) s ≤ 2 := by
        dsimp only [combineStep, combineItemBase, combineNodeBase, combineRankThreshold,
          combineFuel, combineZ, combineFirstRoot, combineNodeCount]
        rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read]
        simp only [hy_ne0, ↓reduceIte]
        rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
          hz_rk, hy_rk]
        simp only [hrk_eq, ne_eq, not_false_eq_true, ↓reduceIte, memoryCost_pure]
        decide
      have hres : (Memory.spec 0).clientResult s
          (combineStep ((itemBase, nodeBase, rt, fuel), (z.rootId, y.rootId, nc, cont))) =
          (z.rootId, y.rootId, nc, 0) := by
        dsimp only [combineStep, combineItemBase, combineNodeBase, combineRankThreshold,
          combineFuel, combineZ, combineFirstRoot, combineNodeCount]
        rw [clientResult_bind_read]
        simp only [hy_ne0, ↓reduceIte]
        rw [clientResult_bind_read, hz_rk, hy_rk]
        simp only [hrk_eq, ne_eq, not_false_eq_true, ↓reduceIte]
        rfl
      have hs' : (Memory.spec 0).clientState s
          (combineStep ((itemBase, nodeBase, rt, fuel), (z.rootId, y.rootId, nc, cont))) = s := by
        dsimp only [combineStep, combineItemBase, combineNodeBase, combineRankThreshold,
          combineFuel, combineZ, combineFirstRoot, combineNodeCount]
        rw [clientState_bind_read]
        simp only [hy_ne0, ↓reduceIte]
        rw [clientState_bind_read, hz_rk, hy_rk]
        simp only [hrk_eq, ne_eq, not_false_eq_true, ↓reduceIte]
        rfl
      have hlt_all : ∀ u ∈ y :: rest, z.rank < u.rank := by
        intro u hu
        rcases List.mem_cons.mp hu with rfl | hu'
        · omega
        · have := hinv.rem_rootList.1 u hu'; omega
      have hinv0 : CombineInv rt w ic₀ nc₀ maxItems maxNodes itemBase nodeBase itemCount origItems
          origEntries newIt z (y :: rest) nc 0 created s :=
        { hinv with cont_zero_lt := fun _ => hlt_all }
      refine ⟨hv, hsafe, ?_, ?_, z, y :: rest, nc, 0, created, ?_, le_rfl, ?_,
        Or.inr ⟨rfl, rfl, rfl, hm, hs'⟩⟩
      · simpa [hhd] using congrArg Memory.State.frontier hs'
      · intro a ha; simp only [hhd, hs'] at ha; exact absurd rfl ha
      · simpa [hhd] using hres
      · simpa [hhd, hs'] using hinv0

private theorem combine_while_spec {rt w ic₀ nc₀ maxItems maxNodes itemBase nodeBase : ℕ}
    {itemCount : ℕ} {origItems : List SHItem} {origEntries : List (SHItem × ℕ)}
    {newIt : SHItem} {z : SHTree} {remRoots : List SHTree} {nc cont kFuel fuel : ℕ}
    {created : ℕ → ℕ} {s : Memory.State}
    (hinv : CombineInv rt w ic₀ nc₀ maxItems maxNodes itemBase nodeBase itemCount origItems
      origEntries newIt z remRoots nc cont created s)
    (hmeas : remRoots.length + (if cont = 0 then 0 else 1) ≤ kFuel)
    (hfuel_ge : shFuelBound rt maxItems ≤ fuel) (hf_fit : Fits w fuel) :
    let d := (itemBase, nodeBase, rt, fuel)
    let a0 := (z.rootId, remRoots.head?.elim 0 SHTree.rootId, nc, cont)
    let guard : ℕ × ℕ × ℕ × ℕ → ℕ × ℕ × ℕ × ℕ → Prop := fun _ a => combineStateCont a ≠ 0
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (boundedWhile guard combineStep d kFuel a0)) ∧
    whileSafe guard combineStep combineStepSafe w d kFuel a0 s ∧
    let res := (Memory.spec 0).clientResult s (boundedWhile guard combineStep d kFuel a0)
    let s' := (Memory.spec 0).clientState s (boundedWhile guard combineStep d kFuel a0)
    s'.frontier = s.frontier ∧
    (∀ a, s'.mem a ≠ s.mem a → InPoolRaw ic₀ nc₀ maxItems maxNodes itemBase nodeBase a) ∧
    ∃ z' remRoots' nc' created',
      res = (z'.rootId, remRoots'.head?.elim 0 SHTree.rootId, nc', 0) ∧
      nc ≤ nc' ∧
      CombineInv rt w ic₀ nc₀ maxItems maxNodes itemBase nodeBase itemCount origItems origEntries
        newIt z' remRoots' nc' 0 created' s' ∧
      (memoryCost (boundedWhile guard combineStep d kFuel a0) s : ℚ) +
        totalPhi rt (z' :: remRoots') ≤ totalPhi rt (z :: remRoots) + 2 := by
  induction kFuel generalizing z remRoots nc cont created s with
  | zero =>
    have hc0 : cont = 0 := by
      have : (if cont = 0 then 0 else 1) = 0 := by omega
      split_ifs at this; assumption
    subst hc0
    dsimp only
    rw [boundedWhile_of_not _ _ _ _ _ (by simp)]
    refine ⟨validHistory_pure w _ _, whileSafe_of_not (by simp), rfl,
      fun _ h => absurd rfl h, z, remRoots, nc, created, rfl, le_rfl, hinv, ?_⟩
    simp [memoryCost_pure]
  | succ k' ih =>
    by_cases hc0 : cont = 0
    · subst hc0
      dsimp only
      rw [boundedWhile_of_not _ _ _ _ _ (by simp)]
      refine ⟨validHistory_pure w _ _, whileSafe_of_not (by simp), rfl,
        fun _ h => absurd rfl h, z, remRoots, nc, created, rfl, le_rfl, hinv, ?_⟩
      simp [memoryCost_pure]
    · have hstep := combineStep_spec hinv hc0 hfuel_ge hf_fit
      rcases hstep with ⟨hv_st, hsafe_st, hfr_st, hmem_st, z₁, rem₁, nc₁, cont₁, created₁,
        hres_st, hnc_st, hinv₁, hbr⟩
      obtain ⟨s₁, hs₁_eq⟩ : ∃ s₁, s₁ = (Memory.spec 0).clientState s
          (combineStep ((itemBase, nodeBase, rt, fuel),
            (z.rootId, remRoots.head?.elim 0 SHTree.rootId, nc, cont))) := ⟨_, rfl⟩
      rw [← hs₁_eq] at hfr_st hmem_st hinv₁ hbr
      have hbw : boundedWhile
          (fun (_ : ℕ × ℕ × ℕ × ℕ) (a : ℕ × ℕ × ℕ × ℕ) => combineStateCont a ≠ 0)
          combineStep (itemBase, nodeBase, rt, fuel) (k' + 1)
          (z.rootId, remRoots.head?.elim 0 SHTree.rootId, nc, cont) =
          (combineStep ((itemBase, nodeBase, rt, fuel),
            (z.rootId, remRoots.head?.elim 0 SHTree.rootId, nc, cont)) >>= fun a' =>
            boundedWhile (fun (_ : ℕ × ℕ × ℕ × ℕ) (a : ℕ × ℕ × ℕ × ℕ) => combineStateCont a ≠ 0)
              combineStep (itemBase, nodeBase, rt, fuel) k' a') := by
        simp [boundedWhile, hc0]
      rcases hbr with ⟨h1, hlt, hphi_st⟩ | ⟨h1, hz1, hrem1, hm_st, _⟩
      · have hmeas₁ : rem₁.length + (if cont₁ = 0 then 0 else 1) ≤ k' := by
          rw [h1]; simp only [hc0, ↓reduceIte] at hmeas; norm_num; omega
        have hih := ih hinv₁ hmeas₁
        rcases hih with ⟨hv_ih, hsafe_ih, hfr_ih, hmem_ih, z', rem', nc', created',
          hres_ih, hnc_ih, hinv', hphi_ih⟩
        refine ⟨?_, ?_, ?_, ?_, z', rem', nc', created', ?_, hnc_st.trans hnc_ih, ?_, ?_⟩
        · rw [hbw]
          refine validHistory_bind_step hv_st ?_
          rw [← hs₁_eq, hres_st]
          exact hv_ih
        · exact whileSafe_succ_pos hc0 hsafe_st (by rw [← hs₁_eq, hres_st]; exact hsafe_ih)
        · rw [hbw, StateTransitionSpec.clientState_bind, ← hs₁_eq, hres_st]
          exact hfr_ih.trans hfr_st
        · intro a ha
          rw [hbw, StateTransitionSpec.clientState_bind, ← hs₁_eq, hres_st] at ha
          by_cases h_eq : ((Memory.spec 0).clientState s₁
              (boundedWhile (fun (_ : ℕ × ℕ × ℕ × ℕ) (a : ℕ × ℕ × ℕ × ℕ) => combineStateCont a ≠ 0)
                combineStep (itemBase, nodeBase, rt, fuel) k'
                (z₁.rootId, rem₁.head?.elim 0 SHTree.rootId, nc₁, cont₁))).mem a = s₁.mem a
          · rw [h_eq] at ha; exact hmem_st a ha
          · exact hmem_ih a h_eq
        · rw [hbw, StateTransitionSpec.clientResult_bind, ← hs₁_eq, hres_st]
          exact hres_ih
        · rw [hbw, StateTransitionSpec.clientState_bind, ← hs₁_eq, hres_st]
          exact hinv'
        · rw [hbw, memoryCost_bind', ← hs₁_eq, hres_st]
          push_cast at hphi_st hphi_ih ⊢; linarith
      · subst h1
        rw [hz1, hrem1] at hinv₁ hres_st
        have hbw0 : boundedWhile
            (fun (_ : ℕ × ℕ × ℕ × ℕ) (a : ℕ × ℕ × ℕ × ℕ) => combineStateCont a ≠ 0)
            combineStep (itemBase, nodeBase, rt, fuel) k'
            (z.rootId, remRoots.head?.elim 0 SHTree.rootId, nc₁, 0) =
            pure (z.rootId, remRoots.head?.elim 0 SHTree.rootId, nc₁, 0) :=
          boundedWhile_of_not _ _ _ _ _ (by simp)
        refine ⟨?_, ?_, ?_, ?_, z, remRoots, nc₁, created₁, ?_, hnc_st, ?_, ?_⟩
        · rw [hbw]
          refine validHistory_bind_step hv_st ?_
          rw [← hs₁_eq, hres_st, hbw0]
          exact validHistory_pure w _ _
        · exact whileSafe_succ_pos hc0 hsafe_st
            (by rw [← hs₁_eq, hres_st]; exact whileSafe_of_not (by simp))
        · rw [hbw, StateTransitionSpec.clientState_bind, ← hs₁_eq, hres_st, hbw0]
          exact hfr_st
        · intro a ha
          rw [hbw, StateTransitionSpec.clientState_bind, ← hs₁_eq, hres_st, hbw0] at ha
          exact hmem_st a ha
        · rw [hbw, StateTransitionSpec.clientResult_bind, ← hs₁_eq, hres_st, hbw0]
          rfl
        · rw [hbw, StateTransitionSpec.clientState_bind, ← hs₁_eq, hres_st, hbw0]
          exact hinv₁
        · rw [hbw, memoryCost_bind', ← hs₁_eq, hres_st, hbw0, memoryCost_pure, add_zero]
          have hm_q : (memoryCost (combineStep ((itemBase, nodeBase, rt, fuel),
              (z.rootId, remRoots.head?.elim 0 SHTree.rootId, nc, cont))) s : ℚ) ≤ 2 := by
            exact_mod_cast hm_st
          linarith

private theorem shInsertLinkRoot_spec {w nodeBase : ℕ} {s : Memory.State}
    {z : SHTree} {remRoots : List SHTree}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hz_ck : s.mem (nodeBase + 12 * z.rootId) = z.ckey)
    (hz_pos : 0 < z.rootId)
    (hz_lt : nodeBase + 12 * z.rootId + 11 < s.frontier)
    (hrk : ∀ u ∈ remRoots, z.rank < u.rank)
    (hrep : RootListRep nodeBase s.mem 0 remRoots)
    (hinfo : ∀ t ∈ remRoots, s.mem (nodeBase + 12 * t.rootId) = t.ckey ∧ 0 < t.rootId ∧
      nodeBase + 12 * t.rootId + 11 < s.frontier)
    (hnd : ((z :: remRoots).map SHTree.rootId).Nodup) :
    let d : Fin 3 → ℕ := ![nodeBase, z.rootId, remRoots.head?.elim 0 SHTree.rootId]
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (shInsertLinkRoot d)) ∧
    memoryCost (shInsertLinkRoot d) s ≤ 7 ∧
    let s' := (Memory.spec 0).clientState s (shInsertLinkRoot d)
    s'.frontier = s.frontier ∧
    (∀ a, s'.mem a ≠ s.mem a →
      a = nodeBase + 12 * z.rootId + 9 ∨ a = nodeBase + 12 * z.rootId + 10 ∨
      a = nodeBase + 12 * z.rootId + 11 ∨
      (∃ r0, remRoots.head? = some r0 ∧ a = nodeBase + 12 * r0.rootId + 9)) ∧
    RootListRep nodeBase s'.mem 0 (z :: remRoots) := by
  have h0_fit : Fits w 0 := h16.of_le (by omega)
  have hz_fit : Fits w z.rootId := hwf.fits_of_lt_frontier (by omega)
  cases remRoots with
  | nil =>
    have hn0 : ([] : List SHTree).head?.elim 0 SHTree.rootId = 0 := rfl
    rw [hn0]
    have hv : (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (shInsertLinkRoot ![nodeBase, z.rootId, 0])) := by
      dsimp only [shInsertLinkRoot]
      simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, ↓reduceIte]
      exact validHistory_write_bind (by omega) h0_fit (validHistory_write_bind (by dsimp; omega)
        h0_fit (validHistory_write (by dsimp; omega) hz_fit))
    have hm : memoryCost (shInsertLinkRoot ![nodeBase, z.rootId, 0]) s ≤ 7 := by
      dsimp only [shInsertLinkRoot]
      simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, ↓reduceIte]
      rw [memoryCost_bind', memoryCost_write, clientState_write, memoryCost_bind',
        memoryCost_write, clientState_write, memoryCost_write]
      decide
    have hs' : (Memory.spec 0).clientState s (shInsertLinkRoot ![nodeBase, z.rootId, 0]) =
        ⟨Function.update (Function.update (Function.update s.mem
          (nodeBase + 12 * z.rootId + 9) 0)
          (nodeBase + 12 * z.rootId + 10) 0)
          (nodeBase + 12 * z.rootId + 11) z.rootId, s.frontier⟩ := by
      dsimp only [shInsertLinkRoot]
      simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, ↓reduceIte]
      rw [clientState_bind_write, clientState_bind_write, clientState_write]
    refine ⟨hv, hm, ?_, ?_, ?_⟩
    · rw [hs']
    · intro a ha
      rw [hs'] at ha; dsimp only at ha
      by_cases h11 : a = nodeBase + 12 * z.rootId + 11
      · exact Or.inr (Or.inr (Or.inl h11))
      · by_cases h10 : a = nodeBase + 12 * z.rootId + 10
        · exact Or.inr (Or.inl h10)
        · by_cases h9 : a = nodeBase + 12 * z.rootId + 9
          · exact Or.inl h9
          · simp only [Function.update_of_ne h11, Function.update_of_ne h10,
              Function.update_of_ne h9] at ha
            exact absurd rfl ha
    · rw [hs']; simp only [RootListRep, suffixMinTree, Option.elim_some]
      refine ⟨hrk, ?_, ?_, ?_, trivial⟩
      · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_self]
      · rw [Function.update_of_ne (by omega), Function.update_self]; rfl
      · rw [Function.update_self]
  | cons r0 rest =>
    have hhd : (r0 :: rest).head?.elim 0 SHTree.rootId = r0.rootId := rfl
    rw [hhd]
    obtain ⟨hr0_ck, hr0_pos, hr0_lt⟩ := hinfo r0 (by simp)
    have hr0_ne0 : r0.rootId ≠ 0 := by omega
    have hr0_fit : Fits w r0.rootId := hwf.fits_of_lt_frontier (by omega)
    have hsm_spec := suffixMinTree_spec (r0 :: rest)
    cases hsm_eq : suffixMinTree (r0 :: rest) with
    | none => rw [hsm_eq] at hsm_spec; simp at hsm_spec
    | some sm =>
      rw [hsm_eq] at hsm_spec
      rcases hsm_spec with ⟨hsm_mem, _⟩
      obtain ⟨hsm_ck, hsm_pos, hsm_lt⟩ := hinfo sm hsm_mem
      have hsm_fit : Fits w sm.rootId := hwf.fits_of_lt_frontier (by omega)
      have hr0_11 : s.mem (nodeBase + 12 * r0.rootId + 11) = sm.rootId := by
        rcases hrep with ⟨_, _, _, h11, _⟩
        simpa [hsm_eq] using h11
      have hv : (Memory.spec w).ValidHistory s
          ((Memory.spec w).clientHistory s
            (shInsertLinkRoot ![nodeBase, z.rootId, r0.rootId])) := by
        dsimp only [shInsertLinkRoot]
        simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, hr0_ne0,
          ↓reduceIte]
        refine validHistory_read_bind (by omega) (validHistory_read_bind (by omega) ?_)
        rw [hr0_11]
        refine validHistory_read_bind (by omega) ?_
        refine validHistory_write_bind (by omega) h0_fit (validHistory_write_bind (by dsimp; omega)
          hr0_fit (validHistory_write_bind (by dsimp; omega) hz_fit ?_))
        split_ifs
        · exact validHistory_write (by dsimp; omega) hz_fit
        · exact validHistory_write (by dsimp; omega) hsm_fit
      have hm : memoryCost (shInsertLinkRoot ![nodeBase, z.rootId, r0.rootId]) s ≤ 7 := by
        dsimp only [shInsertLinkRoot]
        simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, hr0_ne0,
          ↓reduceIte]
        repeat (rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read])
        rw [hr0_11]
        repeat (rw [memoryCost_bind', memoryCost_write, clientState_write])
        split_ifs <;> rw [memoryCost_write]
      have hs' : (Memory.spec 0).clientState s
          (shInsertLinkRoot ![nodeBase, z.rootId, r0.rootId]) =
          ⟨Function.update (Function.update (Function.update (Function.update s.mem
            (nodeBase + 12 * z.rootId + 9) 0)
            (nodeBase + 12 * z.rootId + 10) r0.rootId)
            (nodeBase + 12 * r0.rootId + 9) z.rootId)
            (nodeBase + 12 * z.rootId + 11)
            ((suffixMinTree (z :: r0 :: rest)).elim 0 SHTree.rootId), s.frontier⟩ := by
        dsimp only [shInsertLinkRoot]
        simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, hr0_ne0,
          ↓reduceIte]
        repeat rw [clientState_bind_read]
        rw [hr0_11, hz_ck, hsm_ck]
        repeat rw [clientState_bind_write]
        split_ifs with hck_le <;>
          (rw [clientState_write]; simp [suffixMinTree, hsm_eq, hck_le])
      have hne_zr0 : z.rootId ≠ r0.rootId := by
        rw [List.map_cons, List.nodup_cons] at hnd
        exact fun h => hnd.1 (h ▸ List.mem_cons_self)
      have hrep_out : RootListRep nodeBase ((Memory.spec 0).clientState s
          (shInsertLinkRoot ![nodeBase, z.rootId, r0.rootId])).mem 0 (z :: r0 :: rest) := by
        rw [hs']; dsimp only
        refine ⟨hrk, ?_, ?_, ?_, ?_⟩
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_self]
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_self]; rfl
        · rw [Function.update_self]
        · rcases hrep with ⟨hr0_rk, _, hr0_10, hr0_11', htail⟩
          refine ⟨hr0_rk, ?_, ?_, ?_, ?_⟩
          · rw [Function.update_of_ne (by omega), Function.update_self]
          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hr0_10
          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hr0_11'
          · refine RootListRep.congr (fun t ht j hj => ?_) htail
            have hne_zt : t.rootId ≠ z.rootId := by
              rw [List.map_cons, List.nodup_cons] at hnd
              exact fun h => hnd.1 (h ▸ List.mem_cons_of_mem _ (List.mem_map_of_mem ht))
            have hne_r0t : t.rootId ≠ r0.rootId := by
              rw [List.map_cons, List.nodup_cons, List.map_cons, List.nodup_cons] at hnd
              exact fun h => hnd.2.1 (h ▸ List.mem_map_of_mem ht)
            rcases hj with rfl | rfl | rfl
            · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      refine ⟨hv, hm, ?_, ?_, hrep_out⟩
      · rw [hs']
      · intro a ha
        rw [hs'] at ha; dsimp only at ha
        by_cases h11 : a = nodeBase + 12 * z.rootId + 11
        · exact Or.inr (Or.inr (Or.inl h11))
        · by_cases hr9 : a = nodeBase + 12 * r0.rootId + 9
          · exact Or.inr (Or.inr (Or.inr ⟨r0, rfl, hr9⟩))
          · by_cases h10 : a = nodeBase + 12 * z.rootId + 10
            · exact Or.inr (Or.inl h10)
            · by_cases h9 : a = nodeBase + 12 * z.rootId + 9
              · exact Or.inl h9
              · simp only [Function.update_of_ne h11, Function.update_of_ne hr9,
                  Function.update_of_ne h10, Function.update_of_ne h9] at ha
                exact absurd rfl ha

/-- Insert `(val, origKey)` into the soft heap, maintaining `SHInv`, reporting entry keys and
permutation of items, framing all writes inside `InSHPool`, and paying `O(h.rankThreshold + 1)`
amortized memory cost (`≤ +(240 * h.rankThreshold + 520)` potential slack). -/
theorem shInsert_spec {w ic₀ nc₀ maxItems maxNodes val origKey fuel : ℕ}
    {h : SHHandle} {roots : List SHTree} {created : ℕ → ℕ} {s : Memory.State}
    (hinv : SHInv w ic₀ nc₀ maxItems maxNodes h roots created s)
    (hcap : h.itemCount < maxItems)
    (he_fit : Fits w val) (hk_fit : Fits w origKey)
    (hfuel_ge : shFuelBound h.rankThreshold maxItems ≤ fuel) (hf_fit : Fits w fuel) :
    let d : SHHandle × ℕ × ℕ × ℕ := (h, val, origKey, fuel)
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (shInsert d)) ∧
    shInsertSafe w d s ∧
    let h' := (Memory.spec 0).clientResult s (shInsert d)
    let s' := (Memory.spec 0).clientState s (shInsert d)
    h'.itemBase = h.itemBase ∧
    h'.nodeBase = h.nodeBase ∧
    h'.itemCount = h.itemCount + 1 ∧
    h.nodeCount < h'.nodeCount ∧
    h'.rankThreshold = h.rankThreshold ∧
    s'.frontier = s.frontier ∧
    (∀ a, s'.mem a ≠ s.mem a → InSHPool ic₀ nc₀ maxItems maxNodes h a) ∧
    ∃ roots' created',
      SHInv w ic₀ nc₀ maxItems maxNodes h' roots' created' s' ∧
      (forestItems roots').Perm
        (⟨h.itemCount + 1, val, origKey⟩ :: forestItems roots) ∧
      (∀ p ∈ forestEntries roots',
        (p.1 = ⟨h.itemCount + 1, val, origKey⟩ ∧ origKey ≤ p.2) ∨
        ∃ c₀, (p.1, c₀) ∈ forestEntries roots ∧ c₀ ≤ p.2) ∧
      (memoryCost (shInsert d) s : ℚ) + totalPhi h.rankThreshold roots' ≤
        totalPhi h.rankThreshold roots + (240 * (h.rankThreshold : ℚ) + 520) := by
  have h16 := hinv.fits16
  have hwf := hinv.wf
  have hic_pos : 0 < h.itemCount + 1 := Nat.succ_pos _
  have hnc_pos : 0 < h.nodeCount + 1 := Nat.succ_pos _
  have hnc_succ_le : h.nodeCount + 1 ≤ nc₀ + 2 * (maxItems - ic₀) := by
    have := hinv.ic_le; have := hinv.nc_le; have := hinv.nc_roots_le; omega
  have hnc_succ_max : h.nodeCount + 1 ≤ maxNodes := by have := hinv.pool_cap; omega
  have hi_lt : h.itemBase + 3 * (h.itemCount + 1) + 2 < s.frontier := by
    have := hinv.item_pool_lt; omega
  have hn_lt : h.nodeBase + 12 * (h.nodeCount + 1) + 11 < s.frontier := by
    have := hinv.node_pool_lt; omega
  have hdisj : ∀ j < 12, ∀ k < 3,
      h.nodeBase + 12 * (h.nodeCount + 1) + j ≠ h.itemBase + 3 * (h.itemCount + 1) + k :=
    fun j hj k hk => hinv.pools_disj_node_item hnc_succ_max hcap hj hk
  have hi_fit : Fits w (h.itemCount + 1) := hwf.fits_of_lt_frontier (by omega)
  have hn_fit : Fits w (h.nodeCount + 1) := hwf.fits_of_lt_frontier (by omega)
  have hinit := shInsertInit_spec (rt := h.rankThreshold) h16 hwf hic_pos hnc_pos hi_lt hn_lt
    hdisj hi_fit hn_fit he_fit hk_fit
  rcases hinit with ⟨hv_init, hm_init, hfr_init, hmem_init, hz₀_mem, _, _, _, _⟩
  obtain ⟨s₁, hs₁_eq⟩ : ∃ s₁, s₁ = (Memory.spec 0).clientState s
      (shInsertInit ![h.itemBase, h.nodeBase, h.itemCount + 1, h.nodeCount + 1,
        val, origKey]) := ⟨_, rfl⟩
  rw [← hs₁_eq] at hfr_init hmem_init hz₀_mem
  have hwf₁ : Memory.WellFormed w s₁ := by
    rw [hs₁_eq]; exact wellFormed_clientState hwf hv_init
  let newIt : SHItem := ⟨h.itemCount + 1, val, origKey⟩
  let z₀ : SHTree := .node (h.nodeCount + 1) 0 origKey [newIt] none none
  have hagree_roots_node : ∀ t ∈ roots, ∀ nid ∈ t.nodeIds, ∀ j < 12,
      s₁.mem (h.nodeBase + 12 * nid + j) = s.mem (h.nodeBase + 12 * nid + j) := by
    intro t ht nid hnid j hj
    by_contra hdiff
    have hle := (hinv.nodeIds_range nid (mem_forestNodeIds ht hnid)).2
    have := hinv.nc_max
    rcases hmem_init _ hdiff with ⟨k, hk, heq⟩ | ⟨j', hj', heq⟩
    · exact hinv.pools_disj_node_item (nid := nid) (iid := h.itemCount + 1)
        (by omega) hcap hj hk heq
    · omega
  have hagree_roots_item : ∀ t ∈ roots, ∀ it ∈ t.allItems, ∀ k < 3,
      s₁.mem (h.itemBase + 3 * it.id + k) = s.mem (h.itemBase + 3 * it.id + k) := by
    intro t ht it hit k hk
    by_contra hdiff
    have hle := (hinv.itemIds_range it.id (mem_forestItemIds ht hit)).2
    rcases hmem_init _ hdiff with ⟨k', hk', heq⟩ | ⟨j, hj, heq⟩
    · omega
    · exact hinv.pools_disj_node_item (nid := h.nodeCount + 1) (iid := it.id)
        hnc_succ_max (by omega) hj hk heq.symm
  have hrem_mem₁ : ∀ t ∈ roots, TreeMemRep h.rankThreshold h.itemBase h.nodeBase s₁.mem t := by
    intro t ht
    refine TreeMemRep.congr
      (fun nid hnid j hj => (hagree_roots_node t ht nid hnid j (by omega)).symm)
      (fun it hit k hk => (hagree_roots_item t ht it hit k hk).symm) (hinv.trees_mem t ht)
  have hrem_rl₁ : RootListRep h.nodeBase s₁.mem 0 roots := by
    refine RootListRep.congr (fun t ht j hj => ?_) hinv.rootList
    exact (hagree_roots_node t ht t.rootId t.rootId_mem_nodeIds j (by
      rcases hj with rfl | rfl | rfl <;> omega)).symm
  let created₁ : ℕ → ℕ := fun k => if k = 0 then created 0 + 1 else created k
  have hinv_c : CombineInv h.rankThreshold w ic₀ nc₀ maxItems maxNodes h.itemBase h.nodeBase
      h.itemCount
      (forestItems roots) (forestEntries roots) newIt z₀ roots (h.nodeCount + 1) 1
      created₁ s₁ := by
    refine ⟨h16, hwf₁, hinv.ic_le, hcap, by have := hinv.nc_le; omega, hnc_succ_max,
      hinv.pool_cap, by have := hinv.ic_le; have := hinv.nc_le; have := hinv.nc_roots_le; omega,
      hfr_init ▸ hinv.item_pool_lt, hfr_init ▸ hinv.node_pool_lt, hinv.pools_disj,
      hinv.fits_fuel, ?_, rfl, hz₀_mem, hinv.trees_valid, hrem_mem₁, hrem_rl₁,
      fun _ _ => Nat.zero_le _, fun h => absurd h (by decide),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine SHTree.Valid.node (by simp) (by simp [sizeCap]) (Nat.zero_le _)
        (fun it hit => by rw [List.mem_singleton.mp hit])
        (fun _ it hit => by rw [List.mem_singleton.mp hit])
        (fun h => by simp at h) (fun _ h => by cases h) (fun _ h => by cases h)
        (fun _ h => by cases h) (fun _ h => by cases h)
    · simp only [forestNodeIds, List.flatMap_cons, z₀, SHTree.nodeIds_node, Option.elim_none,
        List.append_nil, List.cons_append, List.nil_append, List.nodup_cons]
      refine ⟨fun h => by have := (hinv.nodeIds_range _ h).2; omega, hinv.nodeIds_nodup⟩
    · intro id hid
      simp only [forestNodeIds, List.flatMap_cons, List.mem_append, z₀, SHTree.nodeIds_node,
        Option.elim_none, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hid
      rcases hid with rfl | h2
      · have := hinv.nc_le; omega
      · have := hinv.nodeIds_range id h2; omega
    · simp only [forestItemIds, List.flatMap_cons, z₀, SHTree.itemIds_node, Option.elim_none,
        List.append_nil, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
        List.nodup_cons, newIt]
      refine ⟨fun hmem => by have := (hinv.itemIds_range _ hmem).2; omega, hinv.itemIds_nodup⟩
    · intro id hid
      simp only [forestItemIds, List.flatMap_cons, List.mem_append, z₀, SHTree.itemIds_node,
        Option.elim_none, List.append_nil, List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false, newIt] at hid
      rcases hid with rfl | h2
      · have := hinv.ic_le; omega
      · have := hinv.itemIds_range id h2; omega
    · intro idx h1 h2 hnot
      have hne_last : idx ≠ h.nodeCount + 1 := fun heq => hnot (by
        simp [forestNodeIds, z₀, heq])
      have h_not_r : idx ∉ forestNodeIds roots := fun h => by
        apply hnot
        simp only [forestNodeIds, List.flatMap_cons, List.mem_append]
        exact Or.inr h
      have hs0 := hinv.dead_nodes_empty idx h1 (by omega) h_not_r
      have h10 : s₁.mem (h.nodeBase + 12 * idx + 4) = s.mem (h.nodeBase + 12 * idx + 4) := by
        by_contra hdiff
        rcases hmem_init _ hdiff with ⟨k, hk, heq⟩ | ⟨j, hj, heq⟩
        · exact hinv.pools_disj_node_item (nid := idx) (iid := h.itemCount + 1) (j := 4)
            (by have := hinv.nc_max; omega) hcap (by decide) hk heq
        · omega
      rw [h10, hs0]
    · simp only [created₁, ↓reduceIte, hinv.created_zero]; have := hinv.ic_le; omega
    · intro k
      have hz0_rk : z₀.rank = 0 := rfl
      rw [List.countP_cons, hz0_rk]
      cases k with
      | zero =>
        have hb0 : 2 * created 1 + roots.countP (fun t => decide (t.rank = 0)) ≤ created 0 :=
          hinv.created_step 0
        have h1 : created₁ 0 = created 0 + 1 := rfl
        have h2 : created₁ 1 = created 1 := rfl
        rw [h1, h2]
        simp only [decide_true, ↓reduceIte]
        omega
      | succ k' =>
        have hb := hinv.created_step (k' + 1)
        have h1 : created₁ (k' + 1) = created (k' + 1) := by simp [created₁]
        have h2 : created₁ (k' + 2) = created (k' + 2) := by simp [created₁]
        rw [h1, h2]
        simp only [show ¬ (0 = k' + 1) by omega, decide_false, Bool.false_eq_true, ↓reduceIte]
        omega
    · intro k
      simp only [List.map_cons, List.sum_cons]
      have hb := hinv.live_rank_le k
      have hcr_z0 : z₀.countRank k = if 0 = k then 1 else 0 := by simp [z₀]
      rw [hcr_z0]
      cases k with
      | zero =>
        have h1 : created₁ 0 = created 0 + 1 := rfl
        rw [h1]; simp only [↓reduceIte]; omega
      | succ k' =>
        have h1 : created₁ (k' + 1) = created (k' + 1) := by simp [created₁]
        rw [h1]; simp only [show ¬ (0 = k' + 1) by omega, ↓reduceIte]; omega
    · intro t ht
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact Nat.zero_le _
      · have := hinv.rank_le t ht'; omega
    · simp [forestItems, forestEntries, z₀]
    · intro p hp
      simp only [forestEntries, List.flatMap_cons, List.mem_append, z₀, SHTree.allEntries_node,
        Option.elim_none, List.append_nil, List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hp
      rcases hp with rfl | h2
      · exact Or.inl ⟨rfl, le_rfl⟩
      · exact Or.inr ⟨p.2, h2, le_rfl⟩
  have hmeas : roots.length + 1 ≤ fuel := by
    have := hinv.nc_roots_le
    have hfb : 100 * (maxItems + 1) ≤ shFuelBound h.rankThreshold maxItems :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have hbw := combine_while_spec hinv_c (kFuel := fuel) (by simpa using hmeas) hfuel_ge hf_fit
  rcases hbw with ⟨hv_bw, hsafe_bw, hfr_bw, hmem_bw, z_end, rem_end, nc_end, created_end,
    hres_bw, hnc_end, hinv_end, hphi_bw⟩
  have hz0_rt : z₀.rootId = h.nodeCount + 1 := rfl
  rw [hz0_rt, ← hinv.firstRoot_eq] at hv_bw hsafe_bw hres_bw hphi_bw
  obtain ⟨s₂, hs₂_eq⟩ : ∃ s₂, s₂ = (Memory.spec 0).clientState s₁
      (boundedWhile (fun (_ : ℕ × ℕ × ℕ × ℕ) (a : ℕ × ℕ × ℕ × ℕ) => combineStateCont a ≠ 0)
        combineStep (h.itemBase, h.nodeBase, h.rankThreshold, fuel) fuel
        (h.nodeCount + 1, h.firstRoot, h.nodeCount + 1, 1)) := ⟨_, rfl⟩
  have hs₂_rw : s₂ = (Memory.spec 0).clientState s₁
      (boundedWhile (fun (_ : ℕ × ℕ × ℕ × ℕ) (a : ℕ × ℕ × ℕ × ℕ) => combineStateCont a ≠ 0)
        combineStep (h.itemBase, h.nodeBase, h.rankThreshold, fuel) fuel
        (z₀.rootId, roots.head?.elim 0 SHTree.rootId, h.nodeCount + 1, 1)) := by
    rw [hz0_rt, ← hinv.firstRoot_eq]; exact hs₂_eq
  rw [← hs₂_rw] at hfr_bw hmem_bw hinv_end
  have hlink_pos_z : 0 < z_end.rootId := by
    have := (hinv_end.nodeIds_range z_end.rootId
      (mem_forestNodeIds (by simp) z_end.rootId_mem_nodeIds)).1
    omega
  have hlink_lt_z : h.nodeBase + 12 * z_end.rootId + 11 < s₂.frontier := by
    have := (hinv_end.nodeIds_range z_end.rootId
      (mem_forestNodeIds (by simp) z_end.rootId_mem_nodeIds)).2
    have := hinv_end.nc_max; have := hinv_end.node_pool_lt; omega
  have hlink_info : ∀ t ∈ rem_end, s₂.mem (h.nodeBase + 12 * t.rootId) = t.ckey ∧
      0 < t.rootId ∧ h.nodeBase + 12 * t.rootId + 11 < s₂.frontier := by
    intro t ht
    have hm := (hinv_end.rem_mem t ht).ckey_eq
    have hrng := hinv_end.nodeIds_range t.rootId
      (mem_forestNodeIds (by simp [ht]) t.rootId_mem_nodeIds)
    have := hinv_end.nc_max; have := hinv_end.node_pool_lt
    exact ⟨hm, by omega, by omega⟩
  have hlink_nd : ((z_end :: rem_end).map SHTree.rootId).Nodup := by
    have hsub : ((z_end :: rem_end).map SHTree.rootId).Sublist
        (forestNodeIds (z_end :: rem_end)) := by
      simp only [forestNodeIds]
      induction (z_end :: rem_end) with
      | nil => simp
      | cons a l ih =>
        simp only [List.map_cons, List.flatMap_cons]
        cases a with
        | node id _ _ _ left right =>
          rw [SHTree.nodeIds_node, SHTree.rootId]
          exact List.Sublist.cons_cons id
            (List.Sublist.trans ih (List.sublist_append_right _ _))
    exact hsub.nodup hinv_end.nodeIds_nodup
  have hlink := shInsertLinkRoot_spec h16 hinv_end.wf hinv_end.z_mem.ckey_eq hlink_pos_z
    hlink_lt_z (hinv_end.cont_zero_lt rfl) hinv_end.rem_rootList hlink_info hlink_nd
  rcases hlink with ⟨hv_lk, hm_lk, hfr_lk, hmem_lk, hrep_lk⟩
  obtain ⟨s₃, hs₃_eq⟩ : ∃ s₃, s₃ = (Memory.spec 0).clientState s₂
      (shInsertLinkRoot ![h.nodeBase, z_end.rootId, rem_end.head?.elim 0 SHTree.rootId]) :=
    ⟨_, rfl⟩
  rw [← hs₃_eq] at hfr_lk hmem_lk hrep_lk
  have hwf₃ : Memory.WellFormed w s₃ := by
    rw [hs₃_eq]; exact wellFormed_clientState hinv_end.wf hv_lk
  have hraw_res : (Memory.spec 0).clientResult s
      (shInsertRaw ![h.itemBase, h.nodeBase, h.firstRoot, h.itemCount, h.nodeCount,
        val, origKey, fuel, h.rankThreshold]) =
      (z_end.rootId, h.itemCount + 1, nc_end) := by
    dsimp only [shInsertRaw, combineStateCont, combineStateFirstRoot, combineStateNodeCount]
    simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    rw [StateTransitionSpec.clientResult_bind, ← hs₁_eq]
    rw [StateTransitionSpec.clientResult_bind, hres_bw, ← hs₂_eq]
    rw [StateTransitionSpec.clientResult_bind]
    rfl
  have hraw_state : (Memory.spec 0).clientState s
      (shInsertRaw ![h.itemBase, h.nodeBase, h.firstRoot, h.itemCount, h.nodeCount,
        val, origKey, fuel, h.rankThreshold]) = s₃ := by
    dsimp only [shInsertRaw, combineStateCont, combineStateFirstRoot, combineStateNodeCount]
    simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    rw [StateTransitionSpec.clientState_bind, ← hs₁_eq]
    rw [StateTransitionSpec.clientState_bind, hres_bw, ← hs₂_eq]
    rw [StateTransitionSpec.clientState_bind, ← hs₃_eq]
    rfl
  have hv_raw : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s
        (shInsertRaw ![h.itemBase, h.nodeBase, h.firstRoot, h.itemCount, h.nodeCount,
          val, origKey, fuel, h.rankThreshold])) := by
    dsimp only [shInsertRaw, combineStateCont, combineStateFirstRoot, combineStateNodeCount]
    simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    refine validHistory_bind_step hv_init ?_
    rw [← hs₁_eq]
    refine validHistory_bind_step hv_bw ?_
    rw [← hs₂_eq, hres_bw]
    exact validHistory_bind_step hv_lk (validHistory_pure w _ _)
  have hsafe_raw : shInsertRawSafe w ![h.itemBase, h.nodeBase, h.firstRoot, h.itemCount,
      h.nodeCount, val, origKey, fuel, h.rankThreshold] s := by
    dsimp only [shInsertRawSafe, combineStateCont]
    simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    refine ⟨h16, hi_fit, hn_fit, ?_⟩
    rw [← hs₁_eq]
    exact hsafe_bw
  have hm_raw : memoryCost (shInsertRaw ![h.itemBase, h.nodeBase, h.firstRoot, h.itemCount,
      h.nodeCount, val, origKey, fuel, h.rankThreshold]) s =
      memoryCost (shInsertInit ![h.itemBase, h.nodeBase, h.itemCount + 1, h.nodeCount + 1,
        val, origKey]) s +
      memoryCost (boundedWhile
        (fun (_ : ℕ × ℕ × ℕ × ℕ) (a : ℕ × ℕ × ℕ × ℕ) => combineStateCont a ≠ 0)
        combineStep (h.itemBase, h.nodeBase, h.rankThreshold, fuel) fuel
        (h.nodeCount + 1, h.firstRoot, h.nodeCount + 1, 1)) s₁ +
      memoryCost (shInsertLinkRoot
        ![h.nodeBase, z_end.rootId, rem_end.head?.elim 0 SHTree.rootId]) s₂ := by
    dsimp only [shInsertRaw, combineStateCont, combineStateFirstRoot, combineStateNodeCount]
    simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    rw [memoryCost_bind', ← hs₁_eq, memoryCost_bind', hres_bw, ← hs₂_eq,
      memoryCost_bind', memoryCost_pure, add_zero, Nat.add_assoc]
  have hmem_raw : ∀ a, s₃.mem a ≠ s.mem a →
      InSHPool ic₀ nc₀ maxItems maxNodes h a := by
    intro a ha
    by_cases h32 : s₃.mem a = s₂.mem a
    · rw [h32] at ha
      by_cases h21 : s₂.mem a = s₁.mem a
      · rw [h21] at ha
        rcases hmem_init _ ha with ⟨k, hk, rfl⟩ | ⟨j, hj, rfl⟩
        · left; have := hinv.ic_le; omega
        · right; have := hinv.nc_le; omega
      · exact hmem_bw a h21
    · rcases hmem_lk a h32 with rfl | rfl | rfl | ⟨r0, hr0, rfl⟩
      · right; have := (hinv_end.nodeIds_range z_end.rootId
          (mem_forestNodeIds (by simp) z_end.rootId_mem_nodeIds)).1
        have := (hinv_end.nodeIds_range z_end.rootId
          (mem_forestNodeIds (by simp) z_end.rootId_mem_nodeIds)).2
        have := hinv_end.nc_max; omega
      · right; have := (hinv_end.nodeIds_range z_end.rootId
          (mem_forestNodeIds (by simp) z_end.rootId_mem_nodeIds)).1
        have := (hinv_end.nodeIds_range z_end.rootId
          (mem_forestNodeIds (by simp) z_end.rootId_mem_nodeIds)).2
        have := hinv_end.nc_max; omega
      · right; have := (hinv_end.nodeIds_range z_end.rootId
          (mem_forestNodeIds (by simp) z_end.rootId_mem_nodeIds)).1
        have := (hinv_end.nodeIds_range z_end.rootId
          (mem_forestNodeIds (by simp) z_end.rootId_mem_nodeIds)).2
        have := hinv_end.nc_max; omega
      · right
        have hr0_mem : r0 ∈ rem_end := by cases rem_end <;> simp_all
        have hrng := hinv_end.nodeIds_range r0.rootId
          (mem_forestNodeIds (by simp [hr0_mem]) r0.rootId_mem_nodeIds)
        have := hinv_end.nc_max; omega
  have hagree_lk_node : ∀ t ∈ z_end :: rem_end, ∀ id ∈ t.nodeIds, ∀ j < 8,
      s₃.mem (h.nodeBase + 12 * id + j) = s₂.mem (h.nodeBase + 12 * id + j) := by
    intro t ht id hid j hj
    by_contra hdiff
    rcases hmem_lk _ hdiff with heq | heq | heq | ⟨r0, _, heq⟩ <;> omega
  have hagree_lk_item : ∀ t ∈ z_end :: rem_end, ∀ it ∈ t.allItems, ∀ k < 3,
      s₃.mem (h.itemBase + 3 * it.id + k) = s₂.mem (h.itemBase + 3 * it.id + k) := by
    intro t ht it hit k hk
    by_contra hdiff
    have hit_le : it.id ≤ maxItems := by
      have := (hinv_end.itemIds_range it.id (mem_forestItemIds ht hit)).2
      omega
    rcases hmem_lk _ hdiff with heq | heq | heq | ⟨r0, hr0, heq⟩
    · have := (hinv_end.nodeIds_range z_end.rootId
        (mem_forestNodeIds (by simp) z_end.rootId_mem_nodeIds)).2
      exact hinv.pools_disj_node_item (by have := hinv_end.nc_max; omega) hit_le (by decide) hk
        heq.symm
    · have := (hinv_end.nodeIds_range z_end.rootId
        (mem_forestNodeIds (by simp) z_end.rootId_mem_nodeIds)).2
      exact hinv.pools_disj_node_item (by have := hinv_end.nc_max; omega) hit_le (by decide) hk
        heq.symm
    · have := (hinv_end.nodeIds_range z_end.rootId
        (mem_forestNodeIds (by simp) z_end.rootId_mem_nodeIds)).2
      exact hinv.pools_disj_node_item (by have := hinv_end.nc_max; omega) hit_le (by decide) hk
        heq.symm
    · have hr0_mem : r0 ∈ rem_end := by cases rem_end <;> simp_all
      have := (hinv_end.nodeIds_range r0.rootId
        (mem_forestNodeIds (by simp [hr0_mem]) r0.rootId_mem_nodeIds)).2
      exact hinv.pools_disj_node_item (by have := hinv_end.nc_max; omega) hit_le (by decide) hk
        heq.symm
  have hinv_final : SHInv w ic₀ nc₀ maxItems maxNodes
      ⟨h.itemBase, h.nodeBase, z_end.rootId, h.itemCount + 1, nc_end, h.rankThreshold⟩
      (z_end :: rem_end) created_end s₃ := by
    refine ⟨h16, hwf₃, by have := hinv.ic_le; dsimp; omega, hcap,
      hinv_end.nc_le, hinv_end.nc_max, hinv.pool_cap,
      by have := hinv_end.nc_roots_le; dsimp; omega,
      hfr_lk ▸ hfr_bw ▸ hinv_end.item_pool_lt, hfr_lk ▸ hfr_bw ▸ hinv_end.node_pool_lt,
      hinv.pools_disj, hinv.fits_fuel, hinv_end.nodeIds_nodup, hinv_end.nodeIds_range,
      hinv_end.itemIds_nodup, hinv_end.itemIds_range, ?_, ?_, ?_, hrep_lk, rfl,
      hinv_end.created_zero, hinv_end.created_step, hinv_end.live_rank_le, hinv_end.rank_le⟩
    · intro idx h1 h2 hnot
      have hs2_d := hinv_end.dead_nodes_empty idx h1 h2 hnot
      have h32 : s₃.mem (h.nodeBase + 12 * idx + 4) = s₂.mem (h.nodeBase + 12 * idx + 4) := by
        by_contra hdiff
        rcases hmem_lk _ hdiff with heq | heq | heq | ⟨r0, _, heq⟩ <;> omega
      rw [h32, hs2_d]
    · intro t ht
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact hinv_end.z_valid
      · exact hinv_end.rem_valid t ht'
    · intro t ht
      refine TreeMemRep.congr (fun id hid j hj => (hagree_lk_node t ht id hid j hj).symm)
        (fun it hit k hk => (hagree_lk_item t ht it hit k hk).symm) ?_
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact hinv_end.z_mem
      · exact hinv_end.rem_mem t ht'
  have hsh_res : (Memory.spec 0).clientResult s (shInsert (h, val, origKey, fuel)) =
      ⟨h.itemBase, h.nodeBase, z_end.rootId, h.itemCount + 1, nc_end, h.rankThreshold⟩ := by
    dsimp only [shInsert, shInsertVal, shInsertOrigKey, shInsertFuel,
      shInsertResItemCount, shInsertResNodeCount]
    rw [StateTransitionSpec.clientResult_bind, hraw_res]
    rfl
  have hsh_state : (Memory.spec 0).clientState s (shInsert (h, val, origKey, fuel)) = s₃ := by
    dsimp only [shInsert, shInsertVal, shInsertOrigKey, shInsertFuel,
      shInsertResItemCount, shInsertResNodeCount]
    rw [StateTransitionSpec.clientState_bind, hraw_state]
    rfl
  have hv_sh : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (shInsert (h, val, origKey, fuel))) := by
    dsimp only [shInsert, shInsertVal, shInsertOrigKey, shInsertFuel,
      shInsertResItemCount, shInsertResNodeCount]
    exact validHistory_bind_step hv_raw (validHistory_pure w _ _)
  have hm_sh : memoryCost (shInsert (h, val, origKey, fuel)) s =
      memoryCost (shInsertRaw ![h.itemBase, h.nodeBase, h.firstRoot, h.itemCount, h.nodeCount,
        val, origKey, fuel, h.rankThreshold]) s := by
    dsimp only [shInsert, shInsertVal, shInsertOrigKey, shInsertFuel,
      shInsertResItemCount, shInsertResNodeCount]
    rw [memoryCost_bind', memoryCost_pure, add_zero]
  refine ⟨hv_sh, hsafe_raw, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    z_end :: rem_end, created_end, ?_, ?_, ?_, ?_⟩
  · simp [hsh_res]
  · simp [hsh_res]
  · simp [hsh_res]
  · rw [hsh_res]; dsimp only; omega
  · simp [hsh_res]
  · rw [hsh_state]; exact hfr_lk.trans (hfr_bw.trans hfr_init)
  · intro a ha; rw [hsh_state] at ha; exact hmem_raw a ha
  · rw [hsh_res, hsh_state]; exact hinv_final
  · exact hinv_end.items_perm
  · exact hinv_end.entries_mono
  · rw [hm_sh, hm_raw]
    have hz0_phi : totalPhi h.rankThreshold (z₀ :: roots) =
        totalPhi h.rankThreshold roots + (240 * (h.rankThreshold : ℚ) + 476) := by
      simp only [totalPhi_cons h.rankThreshold, z₀, SHTree.phi, SHTree.itemPhiSum_node,
        Option.elim_none, SHTree.nodeCount_node, List.length_singleton, Nat.cast_one, one_mul,
        itemPhi_zero h.rankThreshold, add_zero, rootCredit, SHTree.rank, SHTree.left,
        SHTree.right, popDeficit, Option.isSome_none, or_self,
        Bool.false_eq_true, ↓reduceIte]
      ring
    have hm_lk_q : (memoryCost (shInsertLinkRoot
        ![h.nodeBase, z_end.rootId, rem_end.head?.elim 0 SHTree.rootId]) s₂ : ℚ) ≤ 7 := by
      exact_mod_cast hm_lk
    have hbw_q := hphi_bw
    rw [hm_init]
    push_cast
    linarith

end Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap
