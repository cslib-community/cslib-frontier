/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.PriorityQueue.WordRAM.SoftHeap.Model
public import CslibFrontier.Computability.WordRAM.Realization.Absorb
public import CslibFrontier.Computability.WordRAM.Realization.While
public import CslibFrontier.Computability.WordRAM.Realization.Loop
-- `import all` reads `Program`'s private `collectItems*`/`collectNode*` (and `shCollectCorrupted`
-- body), plus `Model`'s private `SHTree.ind`, `ItemListRep.pop`, and `whileSafe_*` lemmas.
import all CslibFrontier.DataStructure.PriorityQueue.WordRAM.SoftHeap.Program
import all CslibFrontier.DataStructure.PriorityQueue.WordRAM.SoftHeap.Model
import CslibFrontier.Computability.WordRAM.Realization.ProgFrame
import CslibFrontier.DataStructure.Memory.Frame
import Mathlib.Tactic.Linarith

/-!
# Corrupted-Item Collection Specification for Word-RAM Soft Heaps

Proves `shCollectCorrupted_spec`: scanning node indices `(nc₀, h.nodeCount]` appends all surviving
corrupted items (`origKey < ckey`) into `outBase[outCount..newOut)`, preserves `SHInv` and memory
framing outside the written output slice, and satisfies
`memoryCost (shCollectCorrupted ...) s ≤ 8 * (h.itemCount - ic₀)`.

## Main results

* `Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap.shCollectCorrupted_spec`: exact permutation,
  framing, and `O(N)` memory-cost specification for corrupted-item harvesting.
-/

public section

namespace Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure Cslib.DataStructure.Memory

private theorem list_length_le_flatMap {α β : Type} {f : α → List β} {xs : List α} {a : α}
    (ha : a ∈ xs) : (f a).length ≤ (xs.flatMap f).length := by
  induction xs with
  | nil => cases ha
  | cons x rest ih =>
    simp only [List.flatMap_cons, List.length_append]
    rcases List.mem_cons.mp ha with rfl | hrest
    · omega
    · have := ih hrest; omega

private theorem mem_forestItemIds_of_mem_entries {roots : List SHTree} {it : SHItem} {ck : ℕ}
    (h : (it, ck) ∈ forestEntries roots) : it.id ∈ forestItemIds roots := by
  induction roots with
  | nil => cases h
  | cons t rest ih =>
    simp only [forestEntries, forestItemIds, List.flatMap_cons, List.mem_append] at h ⊢
    rcases h with ht | hrest
    · exact Or.inl (List.mem_map_of_mem (f := SHItem.id)
        (List.mem_map_of_mem (f := Prod.fst) ht))
    · exact Or.inr (ih hrest)

private def SHTree.nodeEntries : SHTree → List (ℕ × ℕ × List SHItem)
  | .node id _ ck items l r =>
      (id, ck, items) :: (match l with | none => [] | some c => c.nodeEntries) ++
        (match r with | none => [] | some c => c.nodeEntries)

private theorem SHTree.nodeEntries_node (id r ck : ℕ) (items : List SHItem)
    (l r' : Option SHTree) :
    (SHTree.node id r ck items l r').nodeEntries =
      (id, ck, items) :: l.elim [] SHTree.nodeEntries ++
        r'.elim [] SHTree.nodeEntries := by
  cases l <;> cases r' <;> rfl

private theorem SHTree.nodeEntries_map_fst (t : SHTree) :
    t.nodeEntries.map Prod.fst = t.nodeIds := by
  induction t using SHTree.ind with
  | node id r ck items l r' ihL ihR =>
    simp only [SHTree.nodeEntries_node, SHTree.nodeIds_node, List.map_cons,
      List.map_append]
    congr 1
    · congr 1
      cases l with | none => rfl | some c => exact ihL c rfl
    · cases r' with | none => rfl | some c => exact ihR c rfl

private theorem SHTree.nodeEntries_flatMap (t : SHTree) :
    (t.nodeEntries.flatMap (fun e => e.2.2.map (fun it => (it, e.2.1)))) =
      t.allEntries := by
  induction t using SHTree.ind with
  | node id r ck items l r' ihL ihR =>
    simp only [SHTree.nodeEntries_node, SHTree.allEntries_node,
      List.flatMap_append, List.flatMap_cons]
    congr 1
    · congr 1
      cases l with | none => rfl | some c => exact ihL c rfl
    · cases r' with | none => rfl | some c => exact ihR c rfl

private def forestNodeEntries (roots : List SHTree) : List (ℕ × ℕ × List SHItem) :=
  roots.flatMap SHTree.nodeEntries

private theorem forestNodeEntries_map_fst (roots : List SHTree) :
    (forestNodeEntries roots).map Prod.fst = forestNodeIds roots := by
  simp only [forestNodeEntries, forestNodeIds, List.map_flatMap, SHTree.nodeEntries_map_fst]

private theorem forestNodeEntries_flatMap (roots : List SHTree) :
    ((forestNodeEntries roots).flatMap (fun e => e.2.2.map (fun it => (it, e.2.1)))) =
      forestEntries roots := by
  simp only [forestNodeEntries, forestEntries, List.flatMap_assoc, SHTree.nodeEntries_flatMap]

private theorem TreeMemRep.nodeEntries_rep {rt itemBase nodeBase : ℕ} {mem : ℕ → ℕ}
    {t : SHTree} (hrep : TreeMemRep rt itemBase nodeBase mem t) :
    ∀ e ∈ t.nodeEntries, e.1 ≠ 0 ∧ mem (nodeBase + 12 * e.1) = e.2.1 ∧
      ItemListRep itemBase mem (mem (nodeBase + 12 * e.1 + 4))
        (mem (nodeBase + 12 * e.1 + 5)) e.2.2 := by
  induction t using SHTree.ind with
  | node id r ck items l r' ihL ihR =>
    rcases hrep with ⟨hid, h0, _, _, _, hil, _, _, hl, hr⟩
    intro e he
    simp only [SHTree.nodeEntries_node, List.cons_append, List.mem_cons, List.mem_append] at he
    rcases he with rfl | hL | hR
    · exact ⟨hid, h0, hil⟩
    · cases l with
      | none => simp at hL
      | some c => exact ihL c rfl (hl c rfl) e hL
    · cases r' with
      | none => simp at hR
      | some c => exact ihR c rfl (hr c rfl) e hR

private theorem list_filter_fst_eq_singleton {α : Type} {xs : List (ℕ × α)}
    (hnd : (xs.map Prod.fst).Nodup) {e : ℕ × α} (he : e ∈ xs) :
    xs.filter (fun x => decide (x.1 = e.1)) = [e] := by
  induction xs with
  | nil => cases he
  | cons a rest ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.filter_cons]
    rcases List.mem_cons.mp he with rfl | hrest
    · have hnil : rest.filter (fun x => decide (x.1 = e.1)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro x hx hdec
        rw [decide_eq_true_eq] at hdec
        exact hnd.1 (hdec ▸ List.mem_map_of_mem hx)
      simp [hnil]
    · have hne : a.1 ≠ e.1 := fun heq => hnd.1 (heq ▸ List.mem_map_of_mem hrest)
      simp [hne, ih hnd.2 hrest]

private theorem list_flatMap_filter_eq_perm {α : Type} {keys : List ℕ} {xs : List (ℕ × α)}
    (hnd_keys : keys.Nodup) (hsub : ∀ e ∈ xs, e.1 ∈ keys) :
    (keys.flatMap (fun k => xs.filter (fun e => decide (e.1 = k)))).Perm xs := by
  induction keys generalizing xs with
  | nil =>
    cases xs with
    | nil => simp
    | cons e _ => exact absurd (hsub e List.mem_cons_self) List.not_mem_nil
  | cons k rest ih =>
    rw [List.nodup_cons] at hnd_keys
    rw [List.flatMap_cons]
    have hrest_sub : ∀ e ∈ xs.filter (fun e => !decide (e.1 = k)), e.1 ∈ rest := by
      intro e he
      rw [List.mem_filter] at he
      have hne : e.1 ≠ k := by simpa using he.2
      rcases List.mem_cons.mp (hsub e he.1) with heq | hmem
      · exact absurd heq hne
      · exact hmem
    have hih := ih hnd_keys.2 hrest_sub
    have hcongr : rest.flatMap (fun r => (xs.filter (fun e => !decide (e.1 = k))).filter
        (fun e => decide (e.1 = r))) =
        rest.flatMap (fun r => xs.filter (fun e => decide (e.1 = r))) := by
      refine List.flatMap_congr fun r hr => ?_
      rw [List.filter_filter]
      refine List.filter_congr fun e _ => ?_
      have hrk : r ≠ k := fun h => hnd_keys.1 (h ▸ hr)
      cases heq : decide (e.1 = r) <;> cases hkeq : decide (e.1 = k) <;> simp_all
    rw [hcongr] at hih
    exact (List.Perm.append_left _ hih).trans (List.filter_append_perm _ xs)

private def corrVals (ck : ℕ) (items : List SHItem) : List ℕ :=
  (items.filter (fun it => decide (it.origKey < ck))).map SHItem.val

private theorem corrVals_nil (ck : ℕ) : corrVals ck [] = [] := rfl

private theorem corrVals_cons (ck : ℕ) (it : SHItem) (rest : List SHItem) :
    corrVals ck (it :: rest) =
      if it.origKey < ck then it.val :: corrVals ck rest else corrVals ck rest := by
  by_cases h : it.origKey < ck <;> simp [corrVals, h]

private theorem filter_map_entries_eq_corrVals (ck : ℕ) (items : List SHItem) :
    ((items.map (fun it => (it, ck))).filter (fun p => decide (p.1.origKey < p.2))).map
        (fun p => p.1.val) =
      corrVals ck items := by
  induction items with
  | nil => rfl
  | cons it rest ih =>
    rw [corrVals_cons, List.map_cons, List.filter_cons]
    by_cases h : it.origKey < ck <;> simp [h, ih]

private def nodeCorruptedAt (roots : List SHTree) (idx : ℕ) : List ℕ :=
  ((forestNodeEntries roots).filter (fun e => decide (e.1 = idx))).flatMap
    (fun e => corrVals e.2.1 e.2.2)

private def nodeItemCountAt (roots : List SHTree) (idx : ℕ) : ℕ :=
  ((forestNodeEntries roots).filter (fun e => decide (e.1 = idx))).map
    (fun e => e.2.2.length) |>.sum

private theorem nodeCorruptedAt_eq_nil_of_not_mem {roots : List SHTree} {idx : ℕ}
    (hnot : idx ∉ forestNodeIds roots) : nodeCorruptedAt roots idx = [] := by
  have hnil : (forestNodeEntries roots).filter (fun e => decide (e.1 = idx)) = [] :=
    List.filter_eq_nil_iff.mpr fun e he hdec =>
      hnot (forestNodeEntries_map_fst roots ▸ decide_eq_true_eq.mp hdec ▸ List.mem_map_of_mem he)
  simp only [nodeCorruptedAt, hnil, List.flatMap_nil]

private theorem nodeItemCountAt_eq_zero_of_not_mem {roots : List SHTree} {idx : ℕ}
    (hnot : idx ∉ forestNodeIds roots) : nodeItemCountAt roots idx = 0 := by
  have hnil : (forestNodeEntries roots).filter (fun e => decide (e.1 = idx)) = [] :=
    List.filter_eq_nil_iff.mpr fun e he hdec =>
      hnot (forestNodeEntries_map_fst roots ▸ decide_eq_true_eq.mp hdec ▸ List.mem_map_of_mem he)
  simp only [nodeItemCountAt, hnil, List.map_nil, List.sum_nil]

private theorem nodeCorruptedAt_eq_of_mem {roots : List SHTree}
    (hnd : (forestNodeIds roots).Nodup) {e : ℕ × ℕ × List SHItem}
    (he : e ∈ forestNodeEntries roots) :
    nodeCorruptedAt roots e.1 = corrVals e.2.1 e.2.2 := by
  have hnd' : ((forestNodeEntries roots).map Prod.fst).Nodup := by
    rw [forestNodeEntries_map_fst]; exact hnd
  have hf := list_filter_fst_eq_singleton hnd' he
  simp [nodeCorruptedAt, hf]

private theorem nodeItemCountAt_eq_of_mem {roots : List SHTree}
    (hnd : (forestNodeIds roots).Nodup) {e : ℕ × ℕ × List SHItem}
    (he : e ∈ forestNodeEntries roots) :
    nodeItemCountAt roots e.1 = e.2.2.length := by
  have hnd' : ((forestNodeEntries roots).map Prod.fst).Nodup := by
    rw [forestNodeEntries_map_fst]; exact hnd
  have hf := list_filter_fst_eq_singleton hnd' he
  simp [nodeItemCountAt, hf]

private theorem collectItemsStep_spec {w itemBase ck outBase hd tail curOut : ℕ}
    {it : SHItem} {rest : List SHItem} {s : Memory.State}
    (hwf : Memory.WellFormed w s)
    (hil : ItemListRep itemBase s.mem hd tail (it :: rest))
    (hlt_it : itemBase + 3 * it.id + 2 < s.frontier)
    (hlt_out : it.origKey < ck → outBase + curOut < s.frontier) :
    let d : (ℕ × ℕ × ℕ) × (ℕ × ℕ) := ((itemBase, ck, outBase), (it.id, curOut))
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (collectItemsStep d)) ∧
    memoryCost (collectItemsStep d) s ≤ 4 ∧
    (Memory.spec 0).clientResult s (collectItemsStep d) =
      (s.mem (itemBase + 3 * it.id + 2), if it.origKey < ck then curOut + 1 else curOut) ∧
    (Memory.spec 0).clientState s (collectItemsStep d) =
      if it.origKey < ck then ⟨Function.update s.mem (outBase + curOut) it.val, s.frontier⟩
      else s := by
  rcases ItemListRep.pop hil with ⟨_, hval, hkey, _⟩
  dsimp only [collectItemsStep, collectItemBase, collectCKey, collectOutBase,
    collectCurItem, collectCurOut]
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine validHistory_read_bind (by omega) (validHistory_read_bind (by omega)
      (validHistory_read_bind (by omega) ?_))
    rw [hkey]
    split_ifs with hcor
    · rw [hval]
      exact validHistory_write_bind (hlt_out hcor) (hval ▸ hwf.mem_fits _)
        (validHistory_pure w _ _)
    · exact validHistory_pure w _ _
  · repeat (rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read])
    rw [hkey]
    split_ifs
    · simp only [memoryCost_bind', memoryCost_write, memoryCost_pure]; decide
    · simp only [memoryCost_pure]; decide
  · repeat rw [clientResult_bind_read]
    rw [hkey]
    split_ifs
    · simp only [clientResult_bind_write]; rfl
    · rfl
  · repeat rw [clientState_bind_read]
    rw [hkey]
    split_ifs
    · rw [hval]; rfl
    · rfl

private theorem collectItems_while_spec {w itemBase ck outBase outCap : ℕ}
    (items : List SHItem) (hd tail curOut fuel : ℕ) {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hil : ItemListRep itemBase s.mem hd tail items)
    (hfuel : items.length ≤ fuel)
    (hcap : curOut + (corrVals ck items).length ≤ outCap)
    (hlt_items : ∀ it ∈ items, itemBase + 3 * it.id + 2 < s.frontier)
    (hout_lt : outBase + outCap ≤ s.frontier)
    (hout_fit : Fits w (outCap + 1))
    (hdisj : ∀ it ∈ items, ∀ k < 3, ∀ a, outBase + curOut ≤ a → a < outBase + outCap →
      a ≠ itemBase + 3 * it.id + k) :
    let prog := boundedWhile (fun (_ : ℕ × ℕ × ℕ) (a : ℕ × ℕ) => a.1 ≠ 0)
      collectItemsStep (itemBase, ck, outBase) fuel (hd, curOut)
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    whileSafe (fun (_ : ℕ × ℕ × ℕ) (a : ℕ × ℕ) => a.1 ≠ 0)
      collectItemsStep (fun w a _ => Fits w 16 ∧ Fits w (collectCurOut a + 1))
      w (itemBase, ck, outBase) fuel (hd, curOut) s ∧
    memoryCost prog s ≤ 4 * items.length ∧
    ((Memory.spec 0).clientResult s prog).2 = curOut + (corrVals ck items).length ∧
    let s' := (Memory.spec 0).clientState s prog
    s'.frontier = s.frontier ∧
    (∀ a, s'.mem a ≠ s.mem a →
      outBase + curOut ≤ a ∧ a < outBase + curOut + (corrVals ck items).length) ∧
    ∀ i, ∀ hi : i < (corrVals ck items).length,
      s'.mem (outBase + curOut + i) = (corrVals ck items)[i] := by
  induction items generalizing hd tail curOut fuel s with
  | nil =>
    rcases hil with ⟨rfl, _⟩
    simp only [corrVals_nil, List.length_nil, add_zero, mul_zero]
    rw [boundedWhile_of_not _ _ _ _ _ (by simp)]
    refine ⟨validHistory_pure w _ _, whileSafe_of_not (by simp), by simp [memoryCost_pure],
      rfl, rfl, fun _ h => absurd rfl h, fun i hi => by omega⟩
  | cons it rest ih =>
    cases fuel with
    | zero => simp only [List.length_cons] at hfuel; omega
    | succ fuel' =>
      have hid_ne : hd ≠ 0 := hil.head_ne_zero (List.cons_ne_nil _ _)
      rcases ItemListRep.pop hil with ⟨hhd, _, _, hrest⟩
      subst hhd
      have hbw : boundedWhile (fun (_ : ℕ × ℕ × ℕ) (a : ℕ × ℕ) => a.1 ≠ 0)
          collectItemsStep (itemBase, ck, outBase) (fuel' + 1) (it.id, curOut) =
          (collectItemsStep ((itemBase, ck, outBase), (it.id, curOut)) >>= fun st' =>
            boundedWhile (fun (_ : ℕ × ℕ × ℕ) (a : ℕ × ℕ) => a.1 ≠ 0)
              collectItemsStep (itemBase, ck, outBase) fuel' st') := by
        simp only [boundedWhile, ne_eq, hid_ne, not_false_eq_true, ↓reduceIte]
      have hstep := collectItemsStep_spec (ck := ck) (outBase := outBase) (curOut := curOut)
        hwf hil (hlt_items it List.mem_cons_self)
        (fun hcor => by
          simp only [corrVals_cons, hcor, ↓reduceIte, List.length_cons] at hcap
          omega)
      rcases hstep with ⟨hv_st, hm_st, hres_st, hs_st⟩
      set s₁ := (Memory.spec 0).clientState s
        (collectItemsStep ((itemBase, ck, outBase), (it.id, curOut))) with hs₁_def
      have hwf₁ : Memory.WellFormed w s₁ := wellFormed_clientState hwf hv_st
      have hfr₁ : s₁.frontier = s.frontier := by
        rw [hs_st]; split_ifs <;> rfl
      set curOut₁ := if it.origKey < ck then curOut + 1 else curOut
      set nxt := s.mem (itemBase + 3 * it.id + 2)
      have hagree_rest : ∀ it' ∈ rest, ∀ k < 3,
          s.mem (itemBase + 3 * it'.id + k) = s₁.mem (itemBase + 3 * it'.id + k) := by
        intro it' hit' k hk
        rw [hs_st]
        split_ifs with hcor
        · dsimp only
          simp only [corrVals_cons, hcor, ↓reduceIte, List.length_cons] at hcap
          exact (Function.update_of_ne (hdisj it' (List.mem_cons_of_mem _ hit') k hk
            (outBase + curOut) le_rfl (by omega)).symm _ _).symm
        · rfl
      have hrest₁ : ItemListRep itemBase s₁.mem nxt (if nxt = 0 then 0 else tail) rest :=
        ItemListRep.congr hagree_rest hrest
      have hcap₁ : curOut₁ + (corrVals ck rest).length ≤ outCap := by
        by_cases hcor : it.origKey < ck <;>
          simp only [curOut₁, corrVals_cons, hcor, ↓reduceIte, List.length_cons] at hcap ⊢ <;> omega
      have hfit₁ : Fits w (curOut + 1) := hout_fit.of_le (by omega)
      have hih := ih nxt (if nxt = 0 then 0 else tail) curOut₁ fuel' hwf₁ hrest₁
        (by simp only [List.length_cons] at hfuel; omega) hcap₁
        (fun it' hit' => hfr₁ ▸ hlt_items it' (List.mem_cons_of_mem _ hit'))
        (hfr₁ ▸ hout_lt)
        (fun it' hit' k hk a ha1 ha2 =>
          hdisj it' (List.mem_cons_of_mem _ hit') k hk a
            (by dsimp only [curOut₁] at ha1; split_ifs at ha1 <;> omega) ha2)
      rcases hih with ⟨hv_ih, hsafe_ih, hm_ih, hres_ih, hfr_ih, hmem_ih, hget_ih⟩
      dsimp only
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hbw]
        refine validHistory_bind_step hv_st ?_
        rw [hres_st]
        exact hv_ih
      · refine whileSafe_succ_pos hid_ne ⟨h16, hfit₁⟩ ?_
        rw [hres_st]
        exact hsafe_ih
      · rw [hbw, memoryCost_bind', hres_st, ← hs₁_def]
        simp only [List.length_cons]
        omega
      · rw [hbw, StateTransitionSpec.clientResult_bind, hres_st, hres_ih]
        by_cases hcor : it.origKey < ck <;>
          simp only [curOut₁, corrVals_cons, hcor, ↓reduceIte, List.length_cons]; omega
      · rw [hbw, StateTransitionSpec.clientState_bind, hres_st]
        exact hfr_ih.trans hfr₁
      · intro a ha
        rw [hbw, StateTransitionSpec.clientState_bind, hres_st, ← hs₁_def] at ha
        by_cases hcor : it.origKey < ck
        · simp only [corrVals_cons, hcor, ↓reduceIte, List.length_cons]
          by_cases hs₁a : s₁.mem a = s.mem a
          · have ha' := hmem_ih a (hs₁a ▸ ha)
            simp only [curOut₁, hcor, ↓reduceIte] at ha'
            omega
          · simp only [hs_st, hcor, ↓reduceIte] at hs₁a
            by_cases heqa : a = outBase + curOut
            · subst heqa; omega
            · exact absurd (Function.update_of_ne heqa _ _) hs₁a
        · have hs₁_s : s₁ = s := by simp only [hs_st, hcor, ↓reduceIte]
          simp only [corrVals_cons, curOut₁, hcor, ↓reduceIte, hs₁_s] at hmem_ih ha ⊢
          exact hmem_ih a ha
      · intro i hi
        rw [hbw, StateTransitionSpec.clientState_bind, hres_st, ← hs₁_def]
        by_cases hcor : it.origKey < ck
        · simp only [corrVals_cons, hcor, ↓reduceIte] at hi ⊢
          cases i with
          | zero =>
            have hnot_mod : ((Memory.spec 0).clientState s₁
                (boundedWhile (fun (_ : ℕ × ℕ × ℕ) (a : ℕ × ℕ) => a.1 ≠ 0) collectItemsStep
                  (itemBase, ck, outBase) fuel' (nxt, curOut₁))).mem (outBase + curOut + 0) =
                s₁.mem (outBase + curOut + 0) := by
              by_contra hdiff
              have := hmem_ih _ hdiff
              simp only [curOut₁, hcor, ↓reduceIte] at this
              omega
            rw [hnot_mod, hs_st]
            simp only [hcor, ↓reduceIte, Nat.add_zero, Function.update_self]
            rfl
          | succ j =>
            simp only [List.length_cons] at hi
            have hget := hget_ih j (by omega)
            simp only [curOut₁, hcor, ↓reduceIte] at hget ⊢
            have haddr : outBase + curOut + (j + 1) = outBase + (curOut + 1) + j := by omega
            rwa [haddr]
        · simp only [corrVals_cons, curOut₁, hcor, ↓reduceIte] at hi hget_ih ⊢
          exact hget_ih i hi

private theorem collectItems_spec {w itemBase ck outBase hd tail curOut fuel outCap : ℕ}
    {items : List SHItem} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hil : ItemListRep itemBase s.mem hd tail items)
    (hfuel : items.length ≤ fuel)
    (hcap : curOut + (corrVals ck items).length ≤ outCap)
    (hlt_items : ∀ it ∈ items, itemBase + 3 * it.id + 2 < s.frontier)
    (hout_lt : outBase + outCap ≤ s.frontier)
    (hout_fit : Fits w (outCap + 1))
    (hdisj : ∀ it ∈ items, ∀ k < 3, ∀ a, outBase + curOut ≤ a → a < outBase + outCap →
      a ≠ itemBase + 3 * it.id + k) :
    let d : Fin 6 → ℕ := ![itemBase, ck, outBase, hd, curOut, fuel]
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (collectItems d)) ∧
    collectItemsSafe w d s ∧
    memoryCost (collectItems d) s ≤ 4 * items.length ∧
    (Memory.spec 0).clientResult s (collectItems d) = curOut + (corrVals ck items).length ∧
    let s' := (Memory.spec 0).clientState s (collectItems d)
    s'.frontier = s.frontier ∧
    (∀ a, s'.mem a ≠ s.mem a →
      outBase + curOut ≤ a ∧ a < outBase + curOut + (corrVals ck items).length) ∧
    ∀ i, ∀ hi : i < (corrVals ck items).length,
      s'.mem (outBase + curOut + i) = (corrVals ck items)[i] := by
  rcases collectItems_while_spec items hd tail curOut fuel h16 hwf hil hfuel hcap hlt_items
    hout_lt hout_fit hdisj with ⟨hv, hsafe, hm, hres, hfr, hmem, hget⟩
  dsimp only [collectItems]
  rw [memoryCost_bind', memoryCost_pure, add_zero, StateTransitionSpec.clientResult_bind,
    StateTransitionSpec.clientState_bind]
  exact ⟨validHistory_bind_step hv (validHistory_pure w _ _), ⟨h16, hsafe⟩, hm, hres, hfr, hmem,
    hget⟩

private theorem collectNodeStep_head_zero_spec
    {w ic₀ nc₀ maxItems maxNodes outBase fuel : ℕ}
    {h : SHHandle} {roots : List SHTree} {created : ℕ → ℕ} {s : Memory.State}
    (h16 : Fits w 16)
    (hinv : SHInv w ic₀ nc₀ maxItems maxNodes h roots created s)
    {idx curOut : ℕ} (hidx_le : idx ≤ h.nodeCount)
    (hidx_fit : Fits w (idx + 1)) (hhd0 : s.mem (h.nodeBase + 12 * idx + 4) = 0)
    (hcor0 : nodeCorruptedAt roots idx = []) (hcnt0 : nodeItemCountAt roots idx = 0) :
    let prog := collectNodeStep ((h.itemBase, h.nodeBase, outBase, fuel), (idx, curOut))
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    collectNodeStepSafe w ((h.itemBase, h.nodeBase, outBase, fuel), (idx, curOut)) s ∧
    memoryCost prog s ≤ 2 + 4 * nodeItemCountAt roots idx ∧
    (Memory.spec 0).clientResult s prog =
      (idx + 1, curOut + (nodeCorruptedAt roots idx).length) ∧
    ((Memory.spec 0).clientState s prog).frontier = s.frontier ∧
    (∀ a, ((Memory.spec 0).clientState s prog).mem a ≠ s.mem a →
      outBase + curOut ≤ a ∧ a < outBase + curOut + (nodeCorruptedAt roots idx).length) ∧
    SHInv w ic₀ nc₀ maxItems maxNodes h roots created
      ((Memory.spec 0).clientState s prog) ∧
    ∀ i, ∀ hi : i < (nodeCorruptedAt roots idx).length,
      ((Memory.spec 0).clientState s prog).mem (outBase + curOut + i) =
        (nodeCorruptedAt roots idx)[i] := by
  intro prog
  have hn_lt : h.nodeBase + 12 * idx + 11 < s.frontier := by
    have := hinv.nc_max; have := hinv.node_pool_lt; omega
  have hs_eq : (Memory.spec 0).clientState s prog = s := by
    dsimp only [prog, collectNodeStep, collectNodeItemBase, collectNodeBase,
      collectNodeOutBase, collectNodeFuel, collectNodeIdx, collectNodeOutCount]
    repeat rw [clientState_bind_read]
    rw [hhd0]; rfl
  rw [hcor0, hcnt0]
  refine ⟨?_, ⟨h16, hidx_fit, fun hz => absurd hhd0 hz⟩, ?_, ?_, by rw [hs_eq],
    fun a ha => absurd rfl (hs_eq ▸ ha), by rwa [hs_eq], fun _ hi => nomatch hi⟩
  all_goals dsimp only [prog, collectNodeStep, collectNodeItemBase, collectNodeBase,
    collectNodeOutBase, collectNodeFuel, collectNodeIdx, collectNodeOutCount]
  · refine validHistory_read_bind (by omega) (validHistory_read_bind (by omega) ?_)
    rw [hhd0]
    exact validHistory_pure w _ _
  · repeat (rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read])
    simp [hhd0, memoryCost_pure]
  · repeat rw [clientResult_bind_read]
    rw [hhd0]; rfl

private theorem collectNodeStep_spec
    {w ic₀ nc₀ maxItems maxNodes outBase outCount outCap fuel : ℕ}
    {h : SHHandle} {roots : List SHTree} {created : ℕ → ℕ}
    (idx curOut : ℕ) {s : Memory.State}
    (hinv : SHInv w ic₀ nc₀ maxItems maxNodes h roots created s)
    (hidx_gt : nc₀ < idx)
    (hidx_le : idx ≤ h.nodeCount)
    (hfuel : h.itemCount - ic₀ ≤ fuel)
    (hout_ge : outCount ≤ curOut)
    (hout_lt : outBase + outCap ≤ s.frontier)
    (hout_fit : Fits w (outCap + 1))
    (hout_disj : ∀ a, outBase + outCount ≤ a → a < outBase + outCap →
      ¬ InSHPool ic₀ nc₀ maxItems maxNodes h a)
    (hcap : curOut + (nodeCorruptedAt roots idx).length ≤ outCap) :
    let prog := collectNodeStep ((h.itemBase, h.nodeBase, outBase, fuel), (idx, curOut))
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    collectNodeStepSafe w ((h.itemBase, h.nodeBase, outBase, fuel), (idx, curOut)) s ∧
    memoryCost prog s ≤ 2 + 4 * nodeItemCountAt roots idx ∧
    (Memory.spec 0).clientResult s prog = (idx + 1, curOut + (nodeCorruptedAt roots idx).length) ∧
    let s' := (Memory.spec 0).clientState s prog
    s'.frontier = s.frontier ∧
    (∀ a, s'.mem a ≠ s.mem a →
      outBase + curOut ≤ a ∧ a < outBase + curOut + (nodeCorruptedAt roots idx).length) ∧
    SHInv w ic₀ nc₀ maxItems maxNodes h roots created s' ∧
    ∀ i, ∀ hi : i < (nodeCorruptedAt roots idx).length,
      s'.mem (outBase + curOut + i) = (nodeCorruptedAt roots idx)[i] := by
  have h16 := hinv.fits16
  have hwf := hinv.wf
  have hidx_lt : h.nodeBase + 12 * idx + 4 < s.frontier := by
    have := hinv.nc_max; have := hinv.node_pool_lt; omega
  have hidx_fit : Fits w (idx + 1) := by
    have := hinv.nc_max; have := hinv.node_pool_lt
    exact hwf.fits_of_lt_frontier (by omega)
  by_cases hlive : idx ∈ forestNodeIds roots
  · have hmem_fst : idx ∈ (forestNodeEntries roots).map Prod.fst := by
      rw [forestNodeEntries_map_fst]; exact hlive
    rcases List.mem_map.mp hmem_fst with ⟨⟨e_id, e_ck, e_items⟩, he_in, hfst⟩
    dsimp only at hfst
    subst hfst
    have hcor_eq := nodeCorruptedAt_eq_of_mem hinv.nodeIds_nodup he_in
    have hcnt_eq := nodeItemCountAt_eq_of_mem hinv.nodeIds_nodup he_in
    have ⟨t, ht_in, he_t⟩ : ∃ t ∈ roots, (e_id, e_ck, e_items) ∈ t.nodeEntries := by
      simpa [forestNodeEntries, List.mem_flatMap] using he_in
    rcases (hinv.trees_mem t ht_in).nodeEntries_rep (e_id, e_ck, e_items) he_t with
      ⟨_, hck_eq, hil⟩
    dsimp only at hcor_eq hcnt_eq hck_eq hil
    rw [hcor_eq] at hcap
    rw [hcor_eq, hcnt_eq]
    cases e_items with
    | nil =>
      have hhd0 : s.mem (h.nodeBase + 12 * e_id + 4) = 0 :=
        hil.head_eq_zero_iff.mpr rfl
      simpa [hcor_eq, hcnt_eq, corrVals_nil] using
        collectNodeStep_head_zero_spec h16 hinv hidx_le hidx_fit hhd0
          (hcor_eq.trans (by simp [corrVals_nil])) (hcnt_eq.trans rfl)
    | cons it rest =>
      have hhd_ne : s.mem (h.nodeBase + 12 * e_id + 4) ≠ 0 :=
        hil.head_ne_zero (List.cons_ne_nil _ _)
      have hlen_le : (it :: rest).length ≤ fuel := by
        have hlen_fe := hinv.forestEntries_length_le
        have hsub_len : ((it :: rest).map (fun x => (x, e_ck))).length ≤
            (forestEntries roots).length := by
          rw [← forestNodeEntries_flatMap]
          exact list_length_le_flatMap (f := fun e => e.2.2.map (fun x => (x, e.2.1))) he_in
        rw [List.length_map] at hsub_len
        omega
      have hlt_items : ∀ x ∈ it :: rest, h.itemBase + 3 * x.id + 2 < s.frontier := by
        intro x hx
        have hfe : (x, e_ck) ∈ forestEntries roots := by
          rw [← forestNodeEntries_flatMap, List.mem_flatMap]
          exact ⟨(e_id, e_ck, it :: rest), he_in, List.mem_map_of_mem hx⟩
        have hx_le := (hinv.itemIds_range x.id (mem_forestItemIds_of_mem_entries hfe)).2
        have := hinv.ic_max; have := hinv.item_pool_lt; omega
      have hdisj_it : ∀ x ∈ it :: rest, ∀ k < 3, ∀ a,
          outBase + curOut ≤ a → a < outBase + outCap → a ≠ h.itemBase + 3 * x.id + k := by
        intro x hx k hk a ha1 ha2 heqa
        have hfe : (x, e_ck) ∈ forestEntries roots := by
          rw [← forestNodeEntries_flatMap, List.mem_flatMap]
          exact ⟨(e_id, e_ck, it :: rest), he_in, List.mem_map_of_mem hx⟩
        have hxr := hinv.itemIds_range x.id (mem_forestItemIds_of_mem_entries hfe)
        have := hinv.ic_max
        apply hout_disj a (by omega) ha2
        left; constructor <;> omega
      have hcol := collectItems_spec h16 hwf hil hlen_le hcap hlt_items hout_lt hout_fit
        hdisj_it
      rcases hcol with ⟨hv_c, hsafe_c, hm_c, hres_c, hfr_c, hmem_c, hget_c⟩
      have hci_safe : s.mem (h.nodeBase + 12 * e_id + 4) ≠ 0 →
          collectItemsSafe w ![h.itemBase, s.mem (h.nodeBase + 12 * e_id), outBase,
            s.mem (h.nodeBase + 12 * e_id + 4), curOut, fuel] s := by
        intro _
        rw [hck_eq]; exact hsafe_c
      have hv_step : (Memory.spec w).ValidHistory s
          ((Memory.spec w).clientHistory s
            (collectNodeStep ((h.itemBase, h.nodeBase, outBase, fuel), (e_id, curOut)))) := by
        dsimp only [collectNodeStep, collectNodeItemBase, collectNodeBase,
      collectNodeOutBase, collectNodeFuel, collectNodeIdx, collectNodeOutCount]
        refine validHistory_read_bind (by omega) (validHistory_read_bind (by omega) ?_)
        simp only [hhd_ne, ↓reduceIte]
        rw [hck_eq]
        exact validHistory_bind_step hv_c (validHistory_pure w _ _)
      have hm_step : memoryCost
          (collectNodeStep ((h.itemBase, h.nodeBase, outBase, fuel), (e_id, curOut))) s ≤
          2 + 4 * (it :: rest).length := by
        dsimp only [collectNodeStep, collectNodeItemBase, collectNodeBase,
      collectNodeOutBase, collectNodeFuel, collectNodeIdx, collectNodeOutCount]
        repeat (rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read])
        simp only [hhd_ne, ↓reduceIte, memoryCost_bind', memoryCost_pure, add_zero]
        rw [hck_eq]
        omega
      have hres_step : (Memory.spec 0).clientResult s
          (collectNodeStep ((h.itemBase, h.nodeBase, outBase, fuel), (e_id, curOut))) =
          (e_id + 1, curOut + (corrVals e_ck (it :: rest)).length) := by
        dsimp only [collectNodeStep, collectNodeItemBase, collectNodeBase,
      collectNodeOutBase, collectNodeFuel, collectNodeIdx, collectNodeOutCount]
        repeat rw [clientResult_bind_read]
        simp only [hhd_ne, ↓reduceIte, StateTransitionSpec.clientResult_bind]
        rw [hck_eq, hres_c]
        rfl
      have hs_eq : (Memory.spec 0).clientState s
          (collectNodeStep ((h.itemBase, h.nodeBase, outBase, fuel), (e_id, curOut))) =
          (Memory.spec 0).clientState s
            (collectItems ![h.itemBase, e_ck, outBase, s.mem (h.nodeBase + 12 * e_id + 4),
              curOut, fuel]) := by
        dsimp only [collectNodeStep, collectNodeItemBase, collectNodeBase,
      collectNodeOutBase, collectNodeFuel, collectNodeIdx, collectNodeOutCount]
        repeat rw [clientState_bind_read]
        simp only [hhd_ne, ↓reduceIte, hck_eq]
        rw [StateTransitionSpec.clientState_bind]
        rfl
      have hwf' : Memory.WellFormed w ((Memory.spec 0).clientState s
          (collectNodeStep ((h.itemBase, h.nodeBase, outBase, fuel), (e_id, curOut)))) :=
        wellFormed_clientState hwf hv_step
      have hinv' : SHInv w ic₀ nc₀ maxItems maxNodes h roots created
          ((Memory.spec 0).clientState s
            (collectNodeStep ((h.itemBase, h.nodeBase, outBase, fuel), (e_id, curOut)))) := by
        refine hinv.congr_outside hwf' (by rw [hs_eq]; exact hfr_c) (fun a ha => ?_)
        by_contra hdiff
        rw [hs_eq] at hdiff
        have := hmem_c a hdiff
        exact hout_disj a (by omega) (by omega) ha
      refine ⟨hv_step, ⟨h16, hidx_fit, hci_safe⟩, hm_step, hres_step, ?_, ?_, hinv', ?_⟩
      · rw [hs_eq]; exact hfr_c
      · intro a ha; rw [hs_eq] at ha; exact hmem_c a ha
      · intro i hi; rw [hs_eq]; exact hget_c i hi
  · have hhd0 : s.mem (h.nodeBase + 12 * idx + 4) = 0 :=
      hinv.dead_nodes_empty idx hidx_gt hidx_le hlive
    exact collectNodeStep_head_zero_spec h16 hinv hidx_le hidx_fit hhd0
      (nodeCorruptedAt_eq_nil_of_not_mem hlive) (nodeItemCountAt_eq_zero_of_not_mem hlive)

private theorem list_range_map_succ (idx n : ℕ) :
    (List.range (n + 1)).map (fun i => idx + i) =
      idx :: (List.range n).map (fun i => idx + 1 + i) := by
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  simp only [add_zero, Function.comp_def]
  exact congrArg _ (List.map_congr_left fun _ _ => by omega)

private theorem collectNode_iterate_spec
    {w ic₀ nc₀ maxItems maxNodes outBase outCount outCap fuel : ℕ}
    {h : SHHandle} {roots : List SHTree} {created : ℕ → ℕ}
    (n idx curOut : ℕ) {s : Memory.State}
    (hinv : SHInv w ic₀ nc₀ maxItems maxNodes h roots created s)
    (hidx_gt : nc₀ < idx)
    (hidx_end : idx + n ≤ h.nodeCount + 1)
    (hfuel : h.itemCount - ic₀ ≤ fuel)
    (hout_ge : outCount ≤ curOut)
    (hout_lt : outBase + outCap ≤ s.frontier)
    (hout_fit : Fits w (outCap + 1))
    (hout_disj : ∀ a, outBase + outCount ≤ a → a < outBase + outCap →
      ¬ InSHPool ic₀ nc₀ maxItems maxNodes h a)
    (hcap : curOut +
      (((List.range n).map (fun i => idx + i)).flatMap (nodeCorruptedAt roots)).length ≤
        outCap) :
    let keys := (List.range n).map (fun i => idx + i)
    let written := keys.flatMap (nodeCorruptedAt roots)
    let prog := iterate collectNodeStep (h.itemBase, h.nodeBase, outBase, fuel) n (idx, curOut)
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    iterationSafe collectNodeStep collectNodeStepSafe w
      (h.itemBase, h.nodeBase, outBase, fuel) n (idx, curOut) s ∧
    memoryCost prog s ≤ 2 * n + 4 * (keys.map (nodeItemCountAt roots)).sum ∧
    (Memory.spec 0).clientResult s prog = (idx + n, curOut + written.length) ∧
    let s' := (Memory.spec 0).clientState s prog
    s'.frontier = s.frontier ∧
    (∀ a, s'.mem a ≠ s.mem a → outBase + curOut ≤ a ∧ a < outBase + curOut + written.length) ∧
    SHInv w ic₀ nc₀ maxItems maxNodes h roots created s' ∧
    ∀ j, ∀ hj : j < written.length, s'.mem (outBase + curOut + j) = written[j] := by
  induction n generalizing idx curOut s with
  | zero =>
    simp only [List.range_zero, List.map_nil, List.flatMap_nil, List.length_nil, List.sum_nil,
      mul_zero, add_zero]
    refine ⟨validHistory_pure w _ _, trivial, by simp [iterate, memoryCost_pure], rfl, rfl,
      fun _ ha => absurd rfl ha, hinv, fun j hj => by omega⟩
  | succ n ih =>
    have hsplit : (List.range (n + 1)).map (fun i => idx + i) =
        idx :: (List.range n).map (fun i => idx + 1 + i) := list_range_map_succ idx n
    set c₀ := nodeCorruptedAt roots idx with hc₀
    set restKeys := (List.range n).map (fun i => idx + 1 + i) with hrestKeys
    set restWritten := restKeys.flatMap (nodeCorruptedAt roots) with hrestWritten
    have hwritten_eq : ((List.range (n + 1)).map (fun i => idx + i)).flatMap
        (nodeCorruptedAt roots) = c₀ ++ restWritten := by
      rw [hsplit, List.flatMap_cons]
    have hcap₀ : curOut + c₀.length ≤ outCap := by
      rw [hwritten_eq, List.length_append] at hcap; omega
    have hstep := collectNodeStep_spec idx curOut hinv hidx_gt (by omega) hfuel hout_ge
      hout_lt hout_fit hout_disj hcap₀
    rcases hstep with ⟨hv_st, hsafe_st, hm_st, hres_st, hfr_st, hmem_st, hinv₁, hget_st⟩
    set s₁ := (Memory.spec 0).clientState s
      (collectNodeStep ((h.itemBase, h.nodeBase, outBase, fuel), (idx, curOut))) with hs₁
    have hcap_rest : curOut + c₀.length + restWritten.length ≤ outCap := by
      rw [hwritten_eq, List.length_append] at hcap; omega
    have hih := ih (idx + 1) (curOut + c₀.length) hinv₁ (by omega) (by omega)
      (by omega) (hfr_st ▸ hout_lt) hcap_rest
    rcases hih with ⟨hv_ih, hsafe_ih, hm_ih, hres_ih, hfr_ih, hmem_ih, hinv₂, hget_ih⟩
    have hit_eq : iterate collectNodeStep (h.itemBase, h.nodeBase, outBase, fuel) (n + 1)
        (idx, curOut) =
        (collectNodeStep ((h.itemBase, h.nodeBase, outBase, fuel), (idx, curOut)) >>= fun st =>
          iterate collectNodeStep (h.itemBase, h.nodeBase, outBase, fuel) n st) := rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hit_eq]
      refine validHistory_bind_step hv_st ?_
      rw [hres_st]
      exact hv_ih
    · exact ⟨hsafe_st, by rw [hres_st]; exact hsafe_ih⟩
    · rw [hit_eq, memoryCost_bind', hres_st, hsplit, List.map_cons, List.sum_cons,
        ← hc₀, ← hs₁, hrestKeys]
      omega
    · rw [hit_eq, StateTransitionSpec.clientResult_bind, hres_st, ← hc₀, ← hs₁, hres_ih,
        hwritten_eq, List.length_append, hrestWritten, hrestKeys]
      ext <;> dsimp <;> omega
    · rw [hit_eq, StateTransitionSpec.clientState_bind, hres_st]
      exact hfr_ih.trans hfr_st
    · intro a ha
      rw [hit_eq, StateTransitionSpec.clientState_bind, hres_st, ← hc₀, ← hs₁] at ha
      rw [hwritten_eq, List.length_append, hrestWritten, hrestKeys]
      by_cases h1 : s₁.mem a = s.mem a
      · rw [← h1] at ha
        have ha' := hmem_ih a ha
        omega
      · have ha' := hmem_st a h1
        rw [← hc₀] at ha'
        omega
    · rw [hit_eq, StateTransitionSpec.clientState_bind, hres_st]
      exact hinv₂
    · intro j hj
      rw [hit_eq, StateTransitionSpec.clientState_bind, hres_st]
      have hj' : j < c₀.length + restWritten.length := by
        simpa [hwritten_eq, List.length_append] using hj
      by_cases hjc : j < c₀.length
      · have hnot : ((Memory.spec 0).clientState s₁
            (iterate collectNodeStep (h.itemBase, h.nodeBase, outBase, fuel) n
              (idx + 1, curOut + c₀.length))).mem (outBase + curOut + j) =
            s₁.mem (outBase + curOut + j) := by
          by_contra hdiff
          have := hmem_ih _ hdiff
          omega
        rw [hnot, hget_st j hjc]
        simp only [hwritten_eq]
        exact (List.getElem_append_left hjc (bs := restWritten)).symm
      · have hge : c₀.length ≤ j := by omega
        have hk : j - c₀.length < restWritten.length := by omega
        have haddr : outBase + curOut + j = outBase + (curOut + c₀.length) + (j - c₀.length) := by
          omega
        rw [haddr, hget_ih (j - c₀.length) hk]
        simp only [hwritten_eq]
        exact (List.getElem_append_right (h₁ := hge)
          (h₂ := by rw [List.length_append]; omega)).symm

/-- Full specification of `shCollectCorrupted`: scans all allocated nodes `(nc₀, h.nodeCount]`,
appends every surviving corrupted item's `val` (`origKey < ckey`) to `outBase[outCount..]`,
preserves `SHInv` and framing outside `outBase[outCount..newOut)`, and spends
`memoryCost ≤ 8 * (h.itemCount - ic₀)` (uniformly realized via `realizes_shCollectCorrupted`). -/
theorem shCollectCorrupted_spec {w ic₀ nc₀ maxItems maxNodes outBase outCount outCap fuel : ℕ}
    {h : SHHandle} {roots : List SHTree} {created : ℕ → ℕ} {s : Memory.State}
    (hinv : SHInv w ic₀ nc₀ maxItems maxNodes h roots created s)
    (hfuel : h.itemCount - ic₀ ≤ fuel)
    (hout_le : outCount + ((forestEntries roots).filter
      (fun p => decide (p.1.origKey < p.2))).length ≤ outCap)
    (hout_lt : outBase + outCap ≤ s.frontier)
    (hout_fit : Fits w (outCap + 1))
    (hout_disj : ∀ a, outBase + outCount ≤ a → a < outBase + outCap →
      ¬ InSHPool ic₀ nc₀ maxItems maxNodes h a) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s
        (shCollectCorrupted (h, nc₀, outBase, outCount, fuel))) ∧
    shCollectCorruptedSafe w (h, nc₀, outBase, outCount, fuel) s ∧
    let newOut := (Memory.spec 0).clientResult s
      (shCollectCorrupted (h, nc₀, outBase, outCount, fuel))
    let s' := (Memory.spec 0).clientState s
      (shCollectCorrupted (h, nc₀, outBase, outCount, fuel))
    newOut = outCount + ((forestEntries roots).filter
      (fun p => decide (p.1.origKey < p.2))).length ∧
    s'.frontier = s.frontier ∧
    (∀ a, s'.mem a ≠ s.mem a → outBase + outCount ≤ a ∧ a < outBase + newOut) ∧
    SHInv w ic₀ nc₀ maxItems maxNodes h roots created s' ∧
    ((List.range (newOut - outCount)).map (fun i => s'.mem (outBase + outCount + i))).Perm
      (((forestEntries roots).filter (fun p => decide (p.1.origKey < p.2))).map
        (fun p => p.1.val)) ∧
    memoryCost (shCollectCorrupted (h, nc₀, outBase, outCount, fuel)) s ≤
      8 * (h.itemCount - ic₀) := by
  let keys := (List.range (h.nodeCount - nc₀)).map (fun i => (nc₀ + 1) + i)
  let written := keys.flatMap (nodeCorruptedAt roots)
  have hkeys_nd : keys.Nodup := by
    refine List.Nodup.map_on ?_ List.nodup_range
    intro a _ b _ hab; omega
  have hkeys_sub : ∀ e ∈ forestNodeEntries roots, e.1 ∈ keys := by
    intro e he
    have he_id : e.1 ∈ forestNodeIds roots := by
      rw [← forestNodeEntries_map_fst]
      exact List.mem_map_of_mem he
    have hrng := hinv.nodeIds_range e.1 he_id
    dsimp only [keys]
    exact List.mem_map.mpr ⟨e.1 - (nc₀ + 1), List.mem_range.mpr (by omega), by omega⟩
  have hperm_fne :
      (keys.flatMap (fun k => (forestNodeEntries roots).filter (fun e => decide (e.1 = k)))).Perm
        (forestNodeEntries roots) :=
    list_flatMap_filter_eq_perm hkeys_nd hkeys_sub
  have hwritten_eq : written =
      (keys.flatMap (fun k => (forestNodeEntries roots).filter (fun e => decide (e.1 = k)))).flatMap
        (fun e => corrVals e.2.1 e.2.2) :=
    (List.flatMap_assoc ..).symm
  have hcorr_flat :
      (forestNodeEntries roots).flatMap (fun e => corrVals e.2.1 e.2.2) =
        ((forestEntries roots).filter (fun p => decide (p.1.origKey < p.2))).map
          (fun p => p.1.val) := by
    rw [← forestNodeEntries_flatMap, List.filter_flatMap, List.map_flatMap]
    exact List.flatMap_congr fun ⟨_, ck, items⟩ _ => (filter_map_entries_eq_corrVals ck items).symm
  have hwritten_perm : written.Perm
      (((forestEntries roots).filter (fun p => decide (p.1.origKey < p.2))).map
        (fun p => p.1.val)) := by
    rw [hwritten_eq, ← hcorr_flat]
    exact List.Perm.flatMap_right (fun e => corrVals e.2.1 e.2.2) hperm_fne
  have hwritten_len : written.length =
      ((forestEntries roots).filter (fun p => decide (p.1.origKey < p.2))).length := by
    simpa [List.length_map] using hwritten_perm.length_eq
  have hcap_it : outCount + written.length ≤ outCap := by
    rw [hwritten_len]; exact hout_le
  have hit := collectNode_iterate_spec (h.nodeCount - nc₀) (nc₀ + 1) outCount hinv
    (by omega) (by have := hinv.nc_le; omega) hfuel le_rfl hout_lt hout_fit hout_disj hcap_it
  rcases hit with ⟨hv_it, hsafe_it, hm_it, hres_it, hfr_it, hmem_it, hinv', hget_it⟩
  have hsum_cnt : (keys.map (nodeItemCountAt roots)).sum = (forestEntries roots).length := by
    have hperm_len := (List.Perm.flatMap_right
      (fun ⟨_, ck, items⟩ => items.map (fun it => (it, ck))) hperm_fne).length_eq
    rw [forestNodeEntries_flatMap] at hperm_len
    simp only [List.flatMap_assoc, List.length_flatMap, List.length_map] at hperm_len
    exact hperm_len
  have hnc_bound : h.nodeCount - nc₀ ≤ 2 * (h.itemCount - ic₀) := by
    have := hinv.nc_roots_le; omega
  have hlen_bound : (forestEntries roots).length ≤ h.itemCount - ic₀ :=
    hinv.forestEntries_length_le
  have hnc_fit : Fits w (nc₀ + 1) := by
    have := hinv.nc_le; have := hinv.nc_max; have := hinv.node_pool_lt
    exact hinv.wf.fits_of_lt_frontier (by omega)
  have hprog_eq : shCollectCorrupted (h, nc₀, outBase, outCount, fuel) =
      (iterate collectNodeStep (h.itemBase, h.nodeBase, outBase, fuel)
        (h.nodeCount - nc₀) (nc₀ + 1, outCount) >>= fun st => pure st.2) := rfl
  have hres_raw : (Memory.spec 0).clientResult s
      (shCollectCorrupted (h, nc₀, outBase, outCount, fuel)) = outCount + written.length := by
    rw [hprog_eq, StateTransitionSpec.clientResult_bind, hres_it]; rfl
  have hs_raw : (Memory.spec 0).clientState s
      (shCollectCorrupted (h, nc₀, outBase, outCount, fuel)) =
      (Memory.spec 0).clientState s
        (iterate collectNodeStep (h.itemBase, h.nodeBase, outBase, fuel)
          (h.nodeCount - nc₀) (nc₀ + 1, outCount)) := by
    rw [hprog_eq, StateTransitionSpec.clientState_bind]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hprog_eq]
    exact validHistory_bind_step hv_it (validHistory_pure w _ _)
  · exact ⟨hinv.fits16, hinv.nc_le, hnc_fit, hsafe_it⟩
  · rw [hres_raw, hwritten_len]
  · rw [hs_raw]; exact hfr_it
  · intro a ha
    rw [hs_raw] at ha
    rw [hres_raw, ← Nat.add_assoc]
    exact hmem_it a ha
  · rw [hs_raw]; exact hinv'
  · rw [hres_raw, Nat.add_sub_cancel_left]
    have hrange_eq : (List.range written.length).map
        (fun i => ((Memory.spec 0).clientState s
          (shCollectCorrupted (h, nc₀, outBase, outCount, fuel))).mem
            (outBase + outCount + i)) = written := by
      refine List.ext_getElem (by simp) fun i hi₁ _ => ?_
      simp only [List.length_map, List.length_range] at hi₁
      simp only [List.getElem_map, List.getElem_range, hs_raw]
      exact hget_it i hi₁
    exact hrange_eq.symm ▸ hwritten_perm
  · rw [hprog_eq, memoryCost_bind', memoryCost_pure, add_zero]
    rw [hsum_cnt] at hm_it
    omega

end Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap
