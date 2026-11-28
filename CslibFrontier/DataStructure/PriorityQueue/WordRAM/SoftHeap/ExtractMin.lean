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
-- `import all` reads `Program`'s `extractPopItem`/`unlinkLinks`/`extractFixup`/`shExtractMinRaw`
-- (`shExtractMin` body), plus `Model`'s `RootListLinksOnly`, `ItemListRep.pop`, `vec*` lemmas.
import all CslibFrontier.DataStructure.PriorityQueue.WordRAM.SoftHeap.Program
import all CslibFrontier.DataStructure.PriorityQueue.WordRAM.SoftHeap.Model
import CslibFrontier.Foundations.Data.List.Range
import CslibFrontier.Computability.WordRAM.Realization.ProgFrame
import CslibFrontier.DataStructure.Memory.Frame
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Minimum-Extraction Specification for Word-RAM Soft Heaps

Proves `shExtractMin_spec`: extracting the item at the minimum-`ckey` root returns an
`SHExtractResult` with `origKey ≤ popKey ≤ ckey'` for all surviving entries, preserves `SHInv`
and pool framing, removes the extracted item up to multiset permutation, and satisfies
`memoryCost + totalPhi h.rankThreshold roots' ≤ totalPhi h.rankThreshold roots + 250`
independently of `h.rankThreshold`.

## Main results

* `Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap.shExtractMin_spec`: full functional
  correctness, minimality, key-monotonicity, framing, and `O(1)` amortized memory-cost
  specification for `shExtractMin`.
-/

public section

namespace Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure Cslib.DataStructure.Memory

private theorem nodeIds_sub_mid (pre : List SHTree) (t : SHTree) (suf : List SHTree) :
    t.nodeIds.Sublist (forestNodeIds (pre ++ [t] ++ suf)) := by
  have h : pre ++ [t] ++ suf = pre ++ (t :: suf) := List.append_assoc _ _ _
  rw [h, forestNodeIds, List.flatMap_append, List.flatMap_cons]
  exact List.Sublist.trans (List.sublist_append_left _ _) (List.sublist_append_right _ _)

private theorem itemIds_sub_mid (pre : List SHTree) (t : SHTree) (suf : List SHTree) :
    t.itemIds.Sublist (forestItemIds (pre ++ [t] ++ suf)) := by
  have h : pre ++ [t] ++ suf = pre ++ (t :: suf) := List.append_assoc _ _ _
  rw [h, forestItemIds, List.flatMap_append, List.flatMap_cons]
  exact List.Sublist.trans (List.sublist_append_left _ _) (List.sublist_append_right _ _)

private theorem xPop_itemIds_sub {id r ck : ℕ} {it₀ : SHItem} {rest : List SHItem}
    {l r' : Option SHTree} {aid : ℕ}
    (ha : aid ∈ (SHTree.node id r ck rest l r').itemIds) :
    aid ∈ (SHTree.node id r ck (it₀ :: rest) l r').itemIds := by
  simp only [SHTree.itemIds_node, List.map_cons, List.mem_append, List.mem_cons] at ha ⊢
  rcases ha with (h1 | h2) | h3
  · exact Or.inl (Or.inl (Or.inr h1))
  · exact Or.inl (Or.inr h2)
  · exact Or.inr h3

private theorem suffixMinTree_key_id_congr (xs ys : List SHTree)
    (h : xs.map (fun t => (t.rootId, t.ckey)) = ys.map (fun t => (t.rootId, t.ckey))) :
    (suffixMinTree xs).elim (0, 0) (fun t => (t.rootId, t.ckey)) =
      (suffixMinTree ys).elim (0, 0) (fun t => (t.rootId, t.ckey)) := by
  induction xs generalizing ys with
  | nil =>
    cases ys with | nil => rfl | cons _ _ => simp at h
  | cons a r1 ih =>
    cases ys with
    | nil => simp at h
    | cons b r2 =>
      simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at h
      rcases h with ⟨⟨hid, hck⟩, htail⟩
      cases r1 with
      | nil =>
        cases r2 with
        | nil => simp [suffixMinTree, hid, hck]
        | cons _ _ => simp at htail
      | cons a2 r1' =>
        cases r2 with
        | nil => simp at htail
        | cons b2 r2' =>
          have hih := ih (b2 :: r2') htail
          simp only [suffixMinTree]
          cases hsm1 : suffixMinTree (a2 :: r1') with
          | none =>
            have hsp1 := suffixMinTree_spec (a2 :: r1')
            rw [hsm1] at hsp1
            simp at hsp1
          | some sm1 =>
            have hsp2 := suffixMinTree_spec (b2 :: r2')
            cases hsm2 : suffixMinTree (b2 :: r2') with
            | none => rw [hsm2] at hsp2; simp at hsp2
            | some sm2 =>
              rw [hsm1, hsm2] at hih
              simp only [Option.elim_some, Prod.mk.injEq] at hih
              rcases hih with ⟨hsm_id, hsm_ck⟩
              dsimp only
              rw [hck, hsm_ck]
              split_ifs <;> simp [hid, hck, hsm_id, hsm_ck]

private theorem RootListRep.replace_mid {nodeBase prev : ℕ} {mem : ℕ → ℕ}
    {pre suf : List SHTree} {x x' : SHTree}
    (hrt : x'.rootId = x.rootId) (hrk : x'.rank = x.rank) (hck : x'.ckey = x.ckey)
    (hrep : RootListRep nodeBase mem prev (pre ++ [x] ++ suf)) :
    RootListRep nodeBase mem prev (pre ++ [x'] ++ suf) := by
  induction pre generalizing prev with
  | nil =>
    rcases hrep with ⟨h1, h2, h3, h4, h5⟩
    have hcongr : (suffixMinTree (x' :: suf)).elim 0 SHTree.rootId =
        (suffixMinTree (x :: suf)).elim 0 SHTree.rootId := by
      have hkc := suffixMinTree_key_id_congr (x' :: suf) (x :: suf) (by simp [hrt, hck])
      have h1_s := suffixMinTree_spec (x' :: suf)
      have h2_s := suffixMinTree_spec (x :: suf)
      cases hs1 : suffixMinTree (x' :: suf) <;> cases hs2 : suffixMinTree (x :: suf)
      · rfl
      · rw [hs1] at h1_s; simp at h1_s
      · rw [hs2] at h2_s; simp at h2_s
      · rw [hs1, hs2] at hkc; simpa using congrArg Prod.fst hkc
    simp only [List.nil_append, List.singleton_append] at h1 h4 h5 ⊢
    refine ⟨fun u hu => by rw [hrk]; exact h1 u hu, by rw [hrt]; exact h2,
      by rw [hrt]; exact h3, ?_, by rw [hrt]; exact h5⟩
    rw [hrt, hcongr]; exact h4
  | cons a rest ih =>
    rcases hrep with ⟨h1, h2, h3, h4, h5⟩
    have hcongr : (suffixMinTree (a :: (rest ++ [x'] ++ suf))).elim 0 SHTree.rootId =
        (suffixMinTree (a :: (rest ++ [x] ++ suf))).elim 0 SHTree.rootId := by
      have hkc := suffixMinTree_key_id_congr (a :: (rest ++ [x'] ++ suf))
        (a :: (rest ++ [x] ++ suf)) (by simp [hrt, hck])
      cases hs1 : suffixMinTree (a :: (rest ++ [x'] ++ suf)) <;>
        cases hs2 : suffixMinTree (a :: (rest ++ [x] ++ suf))
      · rfl
      · have h1_s := suffixMinTree_spec (a :: (rest ++ [x'] ++ suf))
        rw [hs1] at h1_s; simp at h1_s
      · have h2_s := suffixMinTree_spec (a :: (rest ++ [x] ++ suf))
        rw [hs2] at h2_s; simp at h2_s
      · rw [hs1, hs2] at hkc; simpa using congrArg Prod.fst hkc
    change RootListRep nodeBase mem prev (a :: (rest ++ [x'] ++ suf))
    refine ⟨fun u hu => ?_, h2, ?_, ?_, ih h5⟩
    · simp only [List.mem_append, List.mem_singleton] at hu
      rcases hu with (hr | rfl) | hs
      · exact h1 u (by simp [hr])
      · rw [hrk]; exact h1 x (by simp)
      · exact h1 u (by simp [hs])
    · rw [h3]; cases rest <;> simp [hrt]
    · rw [hcongr]; exact h4

private theorem SHTree.Valid.ckey_le_allEntries {rt lb : ℕ} {t : SHTree} (ht : t.Valid rt lb) :
    ∀ p ∈ t.allEntries, t.ckey ≤ p.2 := by
  cases t with
  | node id r ck items l r' =>
    rcases ht with ⟨_, _, _, _, _, _, _, hl, _, hr⟩
    intro p hp
    simp only [SHTree.allEntries_node, List.mem_append, List.mem_map] at hp
    rcases hp with (⟨it, _, rfl⟩ | hL) | hR
    · exact le_rfl
    · cases l with
      | none => simp at hL
      | some c => exact (hl c rfl).lb_le_allEntries p hL
    · cases r' with
      | none => simp at hR
      | some c => exact (hr c rfl).lb_le_allEntries p hR

private theorem RootListRep.split_append {nodeBase prev : ℕ} {mem : ℕ → ℕ}
    {pre suf : List SHTree} (hrep : RootListRep nodeBase mem prev (pre ++ suf)) :
    RootListLinksOnly nodeBase mem prev suf pre ∧
      RootListRep nodeBase mem (pre.getLast?.elim prev SHTree.rootId) suf := by
  induction pre generalizing prev with
  | nil => exact ⟨trivial, hrep⟩
  | cons a rest ih =>
    rcases hrep with ⟨hrk, h9, h10, _, hrest⟩
    have hih := ih hrest
    refine ⟨⟨hrk, h9, h10, hih.1⟩, ?_⟩
    have hlast : (a :: rest).getLast?.elim prev SHTree.rootId =
        rest.getLast?.elim a.rootId SHTree.rootId := by cases rest <;> rfl
    rw [hlast]
    exact hih.2

private theorem RootListRep.suffixMin_eq {nodeBase prev : ℕ} {mem : ℕ → ℕ}
    {roots : List SHTree} (hne : roots ≠ []) (hrep : RootListRep nodeBase mem prev roots) :
    mem (nodeBase + 12 * (roots.head?.elim 0 SHTree.rootId) + 11) =
      (suffixMinTree roots).elim 0 SHTree.rootId := by
  cases roots with
  | nil => contradiction
  | cons t rest => exact hrep.2.2.2.1

private theorem RootListLinksOnly.skip_second {nodeBase prev : ℕ} {mem : ℕ → ℕ}
    {u x : SHTree} {suf pre : List SHTree}
    (h : RootListLinksOnly nodeBase mem prev (u :: x :: suf) pre) :
    RootListLinksOnly nodeBase mem prev (u :: suf) pre := by
  induction pre generalizing prev with
  | nil => trivial
  | cons a rest ih =>
    rcases h with ⟨hrk, h9, h10, hrest⟩
    refine ⟨fun v hv => hrk v ?_, h9, ?_, ih hrest⟩
    · simp only [List.mem_append, List.mem_cons] at hv ⊢
      rcases hv with h1 | rfl | h2
      · exact Or.inl h1
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inr h2))
    · cases rest with
      | nil => simpa using h10
      | cons b rest2 => simpa using h10

private theorem RootListLinksOnly.replace_head {nodeBase prev : ℕ} {mem : ℕ → ℕ}
    {x x' : SHTree} {suf pre : List SHTree}
    (hroot : x'.rootId = x.rootId) (hrk : x'.rank = x.rank)
    (h : RootListLinksOnly nodeBase mem prev (x :: suf) pre) :
    RootListLinksOnly nodeBase mem prev (x' :: suf) pre := by
  induction pre generalizing prev with
  | nil => trivial
  | cons a rest ih =>
    rcases h with ⟨ha_rk, h9, h10, hrest⟩
    refine ⟨fun v hv => ?_, h9, ?_, ih hrest⟩
    · simp only [List.mem_append, List.mem_cons] at hv
      rcases hv with h1 | rfl | h2
      · exact ha_rk v (List.mem_append_left _ h1)
      · rw [hrk]; exact ha_rk x (by simp)
      · exact ha_rk v (by simp [h2])
    · cases rest with
      | nil => simpa [hroot] using h10
      | cons b rest2 => simpa using h10

private theorem extractPopItem_spec {rt w itemBase nodeBase id r ck : ℕ}
    {it₀ : SHItem} {rest : List SHItem} {l r' : Option SHTree} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hx_mem : TreeMemRep rt itemBase nodeBase s.mem (.node id r ck (it₀ :: rest) l r'))
    (hx_lt : nodeBase + 12 * id + 11 < s.frontier)
    (hit_lt : itemBase + 3 * it₀.id + 2 < s.frontier)
    (hsz_fit : Fits w rest.length)
    (hdisj : ∀ it ∈ it₀ :: rest, ∀ j < 12, ∀ k < 3,
      nodeBase + 12 * id + j ≠ itemBase + 3 * it.id + k) :
    let d : Fin 3 → ℕ := ![itemBase, nodeBase, id]
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (extractPopItem d)) ∧
    memoryCost (extractPopItem d) s ≤ 8 ∧
    (Memory.spec 0).clientResult s (extractPopItem d) = (it₀.val, ck) ∧
    let s' := (Memory.spec 0).clientState s (extractPopItem d)
    s'.frontier = s.frontier ∧
    (∀ a, s'.mem a ≠ s.mem a →
      a = nodeBase + 12 * id + 3 ∨ a = nodeBase + 12 * id + 4 ∨
      a = nodeBase + 12 * id + 5) ∧
    s'.mem (nodeBase + 12 * id) = ck ∧
    s'.mem (nodeBase + 12 * id + 1) = r ∧
    s'.mem (nodeBase + 12 * id + 2) = targetSize rt r ∧
    s'.mem (nodeBase + 12 * id + 3) = rest.length ∧
    ItemListRep itemBase s'.mem (s'.mem (nodeBase + 12 * id + 4))
      (s'.mem (nodeBase + 12 * id + 5)) rest ∧
    (rest = [] → s'.mem (nodeBase + 12 * id + 4) = 0) := by
  have h0_fit : Fits w 0 := h16.of_le (by omega)
  have hck := hx_mem.ckey_eq
  have hrk := hx_mem.rank_eq
  have htgt := hx_mem.target_eq
  have hsz := hx_mem.size_eq
  dsimp only [SHTree.rootId, SHTree.ckey, SHTree.rank, SHTree.items, List.length_cons] at *
  have hpop := ItemListRep.pop hx_mem.items_rep
  rcases hpop with ⟨hhead, hit0, _, hrest_il⟩
  dsimp only [SHTree.rootId] at hhead hrest_il
  let nxt := s.mem (itemBase + 3 * it₀.id + 2)
  have hnxt_fit : Fits w nxt := hwf.mem_fits _
  let base := nodeBase + 12 * id
  let headMem := Function.update s.mem (base + 4) nxt
  let tailMem := if nxt = 0 then Function.update headMem (base + 5) 0 else headMem
  let s' := (Memory.spec 0).clientState s (extractPopItem ![itemBase, nodeBase, id])
  have hnxt_eq : s.mem (itemBase + 3 * it₀.id + 2) = nxt := rfl
  have hsize : rest.length + 1 - 1 = rest.length := Nat.add_sub_cancel _ _
  have hs' : s' = ⟨Function.update tailMem (base + 3) rest.length, s.frontier⟩ := by
    dsimp only [s', extractPopItem]
    simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    repeat rw [clientState_bind_read]
    rw [hck, hhead, hsz, hit0, hnxt_eq, clientState_bind_write, hsize]
    by_cases hnxt : nxt = 0 <;> simp only [tailMem, hnxt, ↓reduceIte, base, headMem]
    all_goals
      repeat rw [clientState_bind_write]
      rfl
  have hv : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (extractPopItem ![itemBase, nodeBase, id])) := by
    dsimp only [extractPopItem]
    simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    refine validHistory_read_bind (by lia) (validHistory_read_bind (by lia) ?_)
    rw [hhead]
    refine validHistory_read_bind (by lia) (validHistory_read_bind (by lia) ?_)
    refine validHistory_read_bind (by lia) ?_
    refine validHistory_write_bind (by lia) hnxt_fit ?_
    rw [hsz, hsize, hnxt_eq]
    by_cases hnxt : nxt = 0
    · simp only [hnxt, ↓reduceIte]
      refine validHistory_write_bind (by dsimp; lia) h0_fit ?_
      exact validHistory_write_bind (by dsimp; lia) hsz_fit (validHistory_pure w _ _)
    · simp only [hnxt, ↓reduceIte]
      exact validHistory_write_bind (by dsimp; lia) hsz_fit (validHistory_pure w _ _)
  have hm : memoryCost (extractPopItem ![itemBase, nodeBase, id]) s ≤ 8 := by
    dsimp only [extractPopItem]
    simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    repeat (rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read])
    rw [hhead, hsz, hit0, hnxt_eq, memoryCost_bind', memoryCost_write, clientState_write]
    by_cases hnxt : nxt = 0 <;>
      simp only [hnxt, ↓reduceIte, memoryCost_bind', memoryCost_write, memoryCost_pure,
        add_zero] <;> decide
  have hres : (Memory.spec 0).clientResult s
      (extractPopItem ![itemBase, nodeBase, id]) = (it₀.val, ck) := by
    dsimp only [extractPopItem]
    simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    repeat rw [clientResult_bind_read]
    rw [hck, hhead, hsz, hit0, hnxt_eq, clientResult_bind_write]
    by_cases hnxt : nxt = 0 <;> simp only [hnxt, ↓reduceIte, clientResult_bind_write] <;> rfl
  have hagree (a : ℕ) (h3 : a ≠ base + 3) (h4 : a ≠ base + 4) (h5 : a ≠ base + 5) :
      s'.mem a = s.mem a := by
    by_cases hnxt : nxt = 0 <;>
      simp only [hs', tailMem, headMem, hnxt, ↓reduceIte,
        Function.update_of_ne h3, Function.update_of_ne h4, Function.update_of_ne h5]
  have hm4 : s'.mem (base + 4) = nxt := by
    by_cases hnxt : nxt = 0 <;>
      simp only [hs', tailMem, headMem, hnxt, ↓reduceIte, Function.update_self,
        Function.update_of_ne (by lia : base + 4 ≠ base + 3),
        Function.update_of_ne (by lia : base + 4 ≠ base + 5)]
  have hm5 : s'.mem (base + 5) = if nxt = 0 then 0 else s.mem (base + 5) := by
    by_cases hnxt : nxt = 0 <;>
      simp only [hs', tailMem, headMem, hnxt, ↓reduceIte, Function.update_self,
        Function.update_of_ne (by lia : base + 5 ≠ base + 3),
        Function.update_of_ne (by lia : base + 5 ≠ base + 4)]
  have hframe (a : ℕ) (ha : s'.mem a ≠ s.mem a) :
      a = base + 3 ∨ a = base + 4 ∨ a = base + 5 := by
    by_contra h
    obtain ⟨h3, h45⟩ := not_or.mp h
    exact ha (hagree a h3 (not_or.mp h45).1 (not_or.mp h45).2)
  have hitems : ItemListRep itemBase s'.mem (s'.mem (base + 4)) (s'.mem (base + 5)) rest := by
    rw [hm4, hm5]
    refine ItemListRep.congr (fun it hit k hk => ?_) hrest_il
    refine (hagree _ ?_ ?_ ?_).symm
    all_goals
      exact (hdisj it (List.mem_cons_of_mem _ hit) _ (by decide) k hk).symm
  have hm3 : s'.mem (base + 3) = rest.length := by rw [hs']; exact Function.update_self _ _ _
  have hnil (hr : rest = []) : s'.mem (base + 4) = 0 := by
    rw [hm4]
    exact (hr ▸ hrest_il).1
  have hfr : s'.frontier = s.frontier := by rw [hs']
  exact ⟨hv, hm, hres, hfr, hframe,
    (hagree base (by lia) (by lia) (by lia)).trans hck,
    (hagree (base + 1) (by lia) (by lia) (by lia)).trans hrk,
    (hagree (base + 2) (by lia) (by lia) (by lia)).trans htgt, hm3, hitems, hnil⟩

private theorem unlinkLinks_spec {w nodeBase : ℕ} {s : Memory.State}
    {pre suf : List SHTree} {x : SHTree}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hrep : RootListRep nodeBase s.mem 0 (pre ++ [x] ++ suf))
    (hinfo : ∀ t ∈ pre ++ [x] ++ suf, 0 < t.rootId ∧ nodeBase + 12 * t.rootId + 11 < s.frontier)
    (hnd : ((pre ++ [x] ++ suf).map SHTree.rootId).Nodup) :
    let d : Fin 3 → ℕ := ![nodeBase, (pre ++ [x] ++ suf).head?.elim 0 SHTree.rootId, x.rootId]
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (unlinkLinks d)) ∧
    memoryCost (unlinkLinks d) s ≤ 4 ∧
    (Memory.spec 0).clientResult s (unlinkLinks d) =
      ((pre ++ suf).head?.elim 0 SHTree.rootId, pre.getLast?.elim 0 SHTree.rootId) ∧
    let s' := (Memory.spec 0).clientState s (unlinkLinks d)
    s'.frontier = s.frontier ∧
    (∀ a, s'.mem a ≠ s.mem a →
      (∃ r0, suf.head? = some r0 ∧ a = nodeBase + 12 * r0.rootId + 9) ∨
      (∃ u, pre.getLast? = some u ∧ a = nodeBase + 12 * u.rootId + 10)) ∧
    RootListLinksOnly nodeBase s'.mem 0 suf pre ∧
    RootListRep nodeBase s'.mem (pre.getLast?.elim 0 SHTree.rootId) suf := by
  have hrep' := hrep
  rw [List.append_assoc] at hrep'
  obtain ⟨hpre_links, hx_rep⟩ := RootListRep.split_append hrep'
  rcases hx_rep with ⟨hx_rk, hx9, hx10, _, hsuf_rep⟩
  have h0_fit : Fits w 0 := h16.of_le (by omega)
  have hx_lt := (hinfo x (by simp)).2
  have hnd' := hnd
  rw [List.append_assoc, List.map_append] at hnd'
  have hnd_disj := list_nodup_append_disj hnd'
  rcases List.eq_nil_or_concat' pre with rfl | ⟨pre', u, rfl⟩
  · have hx9' : s.mem (nodeBase + 12 * x.rootId + 9) = 0 := by simpa using hx9
    cases suf with
    | nil =>
      have hx10' : s.mem (nodeBase + 12 * x.rootId + 10) = 0 := by simpa using hx10
      have hv : (Memory.spec w).ValidHistory s
          ((Memory.spec w).clientHistory s (unlinkLinks ![nodeBase, x.rootId, x.rootId])) := by
        dsimp only [unlinkLinks]; simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one,
                                    Matrix.cons_val]
        refine validHistory_read_bind (by omega) (validHistory_read_bind (by omega) ?_)
        rw [hx9', hx10']
        simp only [ne_eq, not_true_eq_false, ↓reduceIte]
        exact validHistory_pure w _ _
      have hm : memoryCost (unlinkLinks ![nodeBase, x.rootId, x.rootId]) s ≤ 4 := by
        dsimp only [unlinkLinks]; simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one,
                                    Matrix.cons_val]
        repeat (rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read])
        rw [hx9', hx10']
        simp only [ne_eq, not_true_eq_false, ↓reduceIte, memoryCost_pure]
        decide
      have hres : (Memory.spec 0).clientResult s
          (unlinkLinks ![nodeBase, x.rootId, x.rootId]) = (0, 0) := by
        dsimp only [unlinkLinks]; simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one,
                                    Matrix.cons_val]
        repeat rw [clientResult_bind_read]
        rw [hx9', hx10']
        simp only [ne_eq, not_true_eq_false, ↓reduceIte]
        rfl
      have hs' : (Memory.spec 0).clientState s
          (unlinkLinks ![nodeBase, x.rootId, x.rootId]) = s := by
        dsimp only [unlinkLinks]; simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one,
                                    Matrix.cons_val]
        repeat rw [clientState_bind_read]
        rw [hx9', hx10']
        simp only [ne_eq, not_true_eq_false, ↓reduceIte]
        rfl
      refine ⟨by simpa using hv, by simpa using hm, by simpa using hres, ?_, ?_,
        trivial, trivial⟩
      · simpa using congrArg Memory.State.frontier hs'
      · intro a ha; exfalso; simp only [List.nil_append, List.singleton_append,
          List.head?_cons, Option.elim_some] at ha; rw [hs'] at ha; exact ha rfl
    | cons r0 suf' =>
      have hr0_info := hinfo r0 (by simp)
      have hr0_ne0 : r0.rootId ≠ 0 := by omega
      have hx10' : s.mem (nodeBase + 12 * x.rootId + 10) = r0.rootId := by simpa using hx10
      have hv : (Memory.spec w).ValidHistory s
          ((Memory.spec w).clientHistory s (unlinkLinks ![nodeBase, x.rootId, x.rootId])) := by
        dsimp only [unlinkLinks]; simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one,
                                    Matrix.cons_val]
        refine validHistory_read_bind (by omega) (validHistory_read_bind (by omega) ?_)
        rw [hx9', hx10']
        simp only [ne_eq, hr0_ne0, not_false_eq_true, ↓reduceIte, not_true_eq_false]
        exact validHistory_write_bind (by omega) h0_fit (validHistory_pure w _ _)
      have hm : memoryCost (unlinkLinks ![nodeBase, x.rootId, x.rootId]) s ≤ 4 := by
        dsimp only [unlinkLinks]; simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one,
                                    Matrix.cons_val]
        repeat (rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read])
        rw [hx9', hx10']
        simp only [ne_eq, hr0_ne0, not_false_eq_true, ↓reduceIte, not_true_eq_false,
          memoryCost_bind', memoryCost_write, memoryCost_pure]
        decide
      have hres : (Memory.spec 0).clientResult s
          (unlinkLinks ![nodeBase, x.rootId, x.rootId]) = (r0.rootId, 0) := by
        dsimp only [unlinkLinks]; simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one,
                                    Matrix.cons_val]
        repeat rw [clientResult_bind_read]
        rw [hx9', hx10']
        simp only [ne_eq, hr0_ne0, not_false_eq_true, ↓reduceIte, not_true_eq_false,
          clientResult_bind_write]
        rfl
      have hs' : (Memory.spec 0).clientState s
          (unlinkLinks ![nodeBase, x.rootId, x.rootId]) =
          ⟨Function.update s.mem (nodeBase + 12 * r0.rootId + 9) 0, s.frontier⟩ := by
        dsimp only [unlinkLinks]; simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one,
                                    Matrix.cons_val]
        repeat rw [clientState_bind_read]
        rw [hx9', hx10']
        simp only [ne_eq, hr0_ne0, not_false_eq_true, ↓reduceIte, not_true_eq_false]
        rw [clientState_bind_write]
        rfl
      have hsuf' : RootListRep nodeBase
          (Function.update s.mem (nodeBase + 12 * r0.rootId + 9) 0) 0 (r0 :: suf') := by
        rcases hsuf_rep with ⟨hr0_rk, _, hr0_10, hr0_11, htail⟩
        refine ⟨hr0_rk, Function.update_self _ _ _, ?_, ?_, ?_⟩
        · rw [Function.update_of_ne (by omega)]; exact hr0_10
        · rw [Function.update_of_ne (by omega)]; exact hr0_11
        · refine RootListRep.congr (fun t ht j hj => ?_) htail
          have hne : t.rootId ≠ r0.rootId := by
            have hd2 := hnd_disj.2.1
            rw [List.singleton_append, List.map_cons, List.nodup_cons, List.map_cons,
              List.nodup_cons] at hd2
            exact fun heq => hd2.2.1 (heq ▸ List.mem_map_of_mem ht)
          rcases hj with rfl | rfl | rfl <;> exact (Function.update_of_ne (by omega) _ _).symm
      have hhd_l : ([] ++ [x] ++ r0 :: suf').head?.elim 0 SHTree.rootId = x.rootId := rfl
      refine ⟨by rw [hhd_l]; exact hv, by rw [hhd_l]; exact hm, by simpa using hres, ?_, ?_,
        trivial, ?_⟩
      · rw [hhd_l, hs']
      · intro a ha; rw [hhd_l, hs'] at ha; dsimp only at ha
        by_cases ha9 : a = nodeBase + 12 * r0.rootId + 9
        · exact Or.inl ⟨r0, rfl, ha9⟩
        · rw [Function.update_of_ne ha9] at ha; exact absurd rfl ha
      · rw [hhd_l, hs']; exact hsuf'
  · have hu_info := hinfo u (by simp)
    have hu_ne0 : u.rootId ≠ 0 := by omega
    have hu_fit : Fits w u.rootId := hwf.fits_of_lt_frontier (by omega)
    have hlast_u : (pre' ++ [u]).getLast?.elim 0 SHTree.rootId = u.rootId := by
      simp [List.getLast?_append]
    have hx9' : s.mem (nodeBase + 12 * x.rootId + 9) = u.rootId := by
      rw [hx9, hlast_u]
    have hhd_eq : ((pre' ++ [u]) ++ [x] ++ suf).head?.elim 0 SHTree.rootId =
        ((pre' ++ [u]) ++ suf).head?.elim 0 SHTree.rootId := by
      cases pre' <;> rfl
    have hpre_s := rootListLinksOnly_snoc.mp hpre_links
    have hu_9 := hpre_s.2.2.1
    have hpre_sub : RootListLinksOnly nodeBase s.mem 0 (u :: suf) pre' :=
      RootListLinksOnly.skip_second hpre_s.1
    cases suf with
    | nil =>
      have hx10' : s.mem (nodeBase + 12 * x.rootId + 10) = 0 := by simpa using hx10
      have hv : (Memory.spec w).ValidHistory s
          ((Memory.spec w).clientHistory s
            (unlinkLinks ![nodeBase, ((pre' ++ [u]) ++ [x] ++ []).head?.elim 0 SHTree.rootId,
              x.rootId])) := by
        dsimp only [unlinkLinks]; simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one,
                                    Matrix.cons_val]
        refine validHistory_read_bind (by omega) (validHistory_read_bind (by omega) ?_)
        rw [hx9', hx10']
        simp only [ne_eq, not_true_eq_false, ↓reduceIte, hu_ne0, not_false_eq_true]
        exact validHistory_write_bind (by omega) h0_fit (validHistory_pure w _ _)
      have hm : memoryCost (unlinkLinks ![nodeBase,
          ((pre' ++ [u]) ++ [x] ++ []).head?.elim 0 SHTree.rootId, x.rootId]) s ≤ 4 := by
        dsimp only [unlinkLinks]; simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one,
                                    Matrix.cons_val]
        repeat (rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read])
        rw [hx9', hx10']
        simp only [ne_eq, not_true_eq_false, ↓reduceIte, hu_ne0, not_false_eq_true,
          memoryCost_bind', memoryCost_write, memoryCost_pure]
        decide
      have hres : (Memory.spec 0).clientResult s
          (unlinkLinks ![nodeBase, ((pre' ++ [u]) ++ [x] ++ []).head?.elim 0 SHTree.rootId,
            x.rootId]) = (((pre' ++ [u]) ++ []).head?.elim 0 SHTree.rootId, u.rootId) := by
        dsimp only [unlinkLinks]; simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one,
                                    Matrix.cons_val]
        repeat rw [clientResult_bind_read]
        rw [hx9', hx10']
        simp only [ne_eq, not_true_eq_false, ↓reduceIte, hu_ne0, not_false_eq_true]
        rw [clientResult_bind_write]
        simp only [hhd_eq]
        rfl
      have hs' : (Memory.spec 0).clientState s
          (unlinkLinks ![nodeBase, ((pre' ++ [u]) ++ [x] ++ []).head?.elim 0 SHTree.rootId,
            x.rootId]) =
          ⟨Function.update s.mem (nodeBase + 12 * u.rootId + 10) 0, s.frontier⟩ := by
        dsimp only [unlinkLinks]; simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one,
                                    Matrix.cons_val]
        repeat rw [clientState_bind_read]
        rw [hx9', hx10']
        simp only [ne_eq, not_true_eq_false, ↓reduceIte, hu_ne0, not_false_eq_true]
        rw [clientState_bind_write]
        rfl
      have hlinks' : RootListLinksOnly nodeBase
          (Function.update s.mem (nodeBase + 12 * u.rootId + 10) 0) 0 [] (pre' ++ [u]) := by
        rw [rootListLinksOnly_snoc]
        refine ⟨rootListLinksOnly_congr (fun t ht j hj => ?_) hpre_sub,
          (fun _ hm' => nomatch hm'), ?_, Function.update_self _ _ _⟩
        · have hne : t.rootId ≠ u.rootId := by
            have hd1 := hnd_disj.1
            rw [List.map_append, List.map_cons, List.map_nil] at hd1
            have hd1d := list_nodup_append_disj hd1
            exact fun heq => hd1d.2.2 t.rootId (List.mem_map_of_mem ht) (heq ▸ by simp)
          rcases hj with rfl | rfl <;> exact (Function.update_of_ne (by omega) _ _).symm
        · rw [Function.update_of_ne (by omega)]; exact hu_9
      refine ⟨hv, hm, by rw [hlast_u]; exact hres, ?_, ?_, ?_, trivial⟩
      · rw [hs']
      · intro a ha; rw [hs'] at ha; dsimp only at ha
        by_cases ha10 : a = nodeBase + 12 * u.rootId + 10
        · exact Or.inr ⟨u, by simp [List.getLast?_append], ha10⟩
        · rw [Function.update_of_ne ha10] at ha; exact absurd rfl ha
      · rw [hs']; exact hlinks'
    | cons r0 suf' =>
      have hr0_info := hinfo r0 (by simp)
      have hr0_ne0 : r0.rootId ≠ 0 := by omega
      have hr0_fit : Fits w r0.rootId := hwf.fits_of_lt_frontier (by omega)
      have hx10' : s.mem (nodeBase + 12 * x.rootId + 10) = r0.rootId := by simpa using hx10
      have hne_ur0 : u.rootId ≠ r0.rootId := fun heq =>
        hnd_disj.2.2 u.rootId (by simp) (heq ▸ by simp)
      have hv : (Memory.spec w).ValidHistory s
          ((Memory.spec w).clientHistory s
            (unlinkLinks ![nodeBase,
              ((pre' ++ [u]) ++ [x] ++ r0 :: suf').head?.elim 0 SHTree.rootId,
              x.rootId])) := by
        dsimp only [unlinkLinks]; simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one,
                                    Matrix.cons_val]
        refine validHistory_read_bind (by omega) (validHistory_read_bind (by omega) ?_)
        rw [hx9', hx10']
        simp only [ne_eq, hr0_ne0, hu_ne0, not_false_eq_true, ↓reduceIte]
        exact validHistory_write_bind (by omega) hu_fit
          (validHistory_write_bind (by dsimp; omega) hr0_fit (validHistory_pure w _ _))
      have hm : memoryCost (unlinkLinks ![nodeBase,
          ((pre' ++ [u]) ++ [x] ++ r0 :: suf').head?.elim 0 SHTree.rootId, x.rootId]) s ≤ 4 := by
        dsimp only [unlinkLinks]; simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one,
                                    Matrix.cons_val]
        repeat (rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read])
        rw [hx9', hx10']
        simp only [ne_eq, hr0_ne0, hu_ne0, not_false_eq_true, ↓reduceIte,
          memoryCost_bind', memoryCost_write, memoryCost_pure]
        decide
      have hres : (Memory.spec 0).clientResult s
          (unlinkLinks ![nodeBase,
            ((pre' ++ [u]) ++ [x] ++ r0 :: suf').head?.elim 0 SHTree.rootId,
            x.rootId]) =
          (((pre' ++ [u]) ++ r0 :: suf').head?.elim 0 SHTree.rootId, u.rootId) := by
        dsimp only [unlinkLinks]; simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one,
                                    Matrix.cons_val]
        repeat rw [clientResult_bind_read]
        rw [hx9', hx10']
        simp only [ne_eq, hr0_ne0, hu_ne0, not_false_eq_true, ↓reduceIte]
        rw [clientResult_bind_write]
        simp only [hhd_eq]
        rfl
      have hs' : (Memory.spec 0).clientState s
          (unlinkLinks ![nodeBase,
            ((pre' ++ [u]) ++ [x] ++ r0 :: suf').head?.elim 0 SHTree.rootId,
            x.rootId]) =
          ⟨Function.update (Function.update s.mem (nodeBase + 12 * r0.rootId + 9) u.rootId)
            (nodeBase + 12 * u.rootId + 10) r0.rootId, s.frontier⟩ := by
        dsimp only [unlinkLinks]; simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one,
                                    Matrix.cons_val]
        repeat rw [clientState_bind_read]
        rw [hx9', hx10']
        simp only [ne_eq, hr0_ne0, hu_ne0, not_false_eq_true, ↓reduceIte]
        rw [clientState_bind_write]
        rfl
      have hlinks' : RootListLinksOnly nodeBase
          (Function.update (Function.update s.mem (nodeBase + 12 * r0.rootId + 9) u.rootId)
            (nodeBase + 12 * u.rootId + 10) r0.rootId) 0 (r0 :: suf') (pre' ++ [u]) := by
        rw [rootListLinksOnly_snoc]
        refine ⟨rootListLinksOnly_congr (fun t ht j hj => ?_) hpre_sub, ?_, ?_, ?_⟩
        · have hne1 : t.rootId ≠ u.rootId := by
            have hd1 := hnd_disj.1
            rw [List.map_append, List.map_cons, List.map_nil] at hd1
            exact fun heq => (list_nodup_append_disj hd1).2.2 t.rootId
              (List.mem_map_of_mem ht) (heq ▸ by simp)
          have hne2 : t.rootId ≠ r0.rootId := fun heq =>
            hnd_disj.2.2 t.rootId (List.mem_map_of_mem (List.mem_append_left _ ht))
              (List.mem_map.mpr ⟨r0, by simp, heq.symm⟩)
          rcases hj with rfl | rfl <;>
            exact (Function.update_of_ne (by omega) _ _).trans
              (Function.update_of_ne (by omega) _ _) |>.symm
        · intro v hv
          have hu_lt_x : u.rank < x.rank := hpre_s.2.1 x (by simp)
          have hx_lt_v : x.rank < v.rank := hx_rk v hv
          omega
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hu_9
        · exact Function.update_self _ _ _
      have hsuf' : RootListRep nodeBase
          (Function.update (Function.update s.mem (nodeBase + 12 * r0.rootId + 9) u.rootId)
            (nodeBase + 12 * u.rootId + 10) r0.rootId) u.rootId (r0 :: suf') := by
        rcases hsuf_rep with ⟨hr0_rk, _, hr0_10, hr0_11, htail⟩
        refine ⟨hr0_rk, ?_, ?_, ?_, ?_⟩
        · rw [Function.update_of_ne (by omega), Function.update_self]
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hr0_10
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hr0_11
        · refine RootListRep.congr (fun t ht j hj => ?_) htail
          have hne1 : t.rootId ≠ r0.rootId := by
            have hd2 := hnd_disj.2.1
            rw [List.singleton_append, List.map_cons, List.nodup_cons, List.map_cons,
              List.nodup_cons] at hd2
            exact fun heq => hd2.2.1 (heq ▸ List.mem_map_of_mem ht)
          have hne2 : t.rootId ≠ u.rootId := fun heq =>
            hnd_disj.2.2 u.rootId (by simp)
              (List.mem_map.mpr ⟨t, by simp [ht], heq⟩)
          rcases hj with rfl | rfl | rfl <;>
            exact (Function.update_of_ne (by omega) _ _).trans
              (Function.update_of_ne (by omega) _ _) |>.symm
      refine ⟨hv, hm, by rw [hlast_u]; exact hres, ?_, ?_, ?_, ?_⟩
      · rw [hs']
      · intro a ha; rw [hs'] at ha; dsimp only at ha
        by_cases ha10 : a = nodeBase + 12 * u.rootId + 10
        · exact Or.inr ⟨u, by simp [List.getLast?_append], ha10⟩
        · by_cases ha9 : a = nodeBase + 12 * r0.rootId + 9
          · exact Or.inl ⟨r0, rfl, ha9⟩
          · rw [Function.update_of_ne ha10, Function.update_of_ne ha9] at ha
            exact absurd rfl ha
      · rw [hs']; exact hlinks'
      · rw [hs', hlast_u]; exact hsuf'

private theorem extractUnlinkLeaf_spec {w nodeBase fuel : ℕ} {s : Memory.State}
    {pre suf : List SHTree} {x : SHTree}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hrep : RootListRep nodeBase s.mem 0 (pre ++ [x] ++ suf))
    (hinfo : ∀ t ∈ pre ++ [x] ++ suf, s.mem (nodeBase + 12 * t.rootId) = t.ckey ∧
      0 < t.rootId ∧ nodeBase + 12 * t.rootId + 11 < s.frontier)
    (hnd : ((pre ++ [x] ++ suf).map SHTree.rootId).Nodup)
    (hfuel : pre.length ≤ fuel) :
    let d : Fin 4 → ℕ :=
      ![nodeBase, (pre ++ [x] ++ suf).head?.elim 0 SHTree.rootId, x.rootId, fuel]
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (extractUnlinkLeaf d)) ∧
    extractUnlinkLeafSafe w d s ∧
    memoryCost (extractUnlinkLeaf d) s ≤ 4 + 6 * pre.length ∧
    (Memory.spec 0).clientResult s (extractUnlinkLeaf d) =
      (pre ++ suf).head?.elim 0 SHTree.rootId ∧
    let s' := (Memory.spec 0).clientState s (extractUnlinkLeaf d)
    s'.frontier = s.frontier ∧
    (∀ a, s'.mem a ≠ s.mem a →
      (∃ t ∈ pre ++ suf, ∃ j, (j = 9 ∨ j = 10 ∨ j = 11) ∧ a = nodeBase + 12 * t.rootId + j)) ∧
    RootListRep nodeBase s'.mem 0 (pre ++ suf) := by
  have hun := unlinkLinks_spec h16 hwf hrep
    (fun t ht => ⟨(hinfo t ht).2.1, (hinfo t ht).2.2⟩) hnd
  rcases hun with ⟨hv_u, hm_u, hres_u, hfr_u, hmem_u, hlinks_u, hsuf_u⟩
  obtain ⟨s₁, hs₁_eq⟩ : ∃ s₁, s₁ = (Memory.spec 0).clientState s
      (unlinkLinks ![nodeBase, (pre ++ [x] ++ suf).head?.elim 0 SHTree.rootId, x.rootId]) :=
    ⟨_, rfl⟩
  rw [← hs₁_eq] at hfr_u hmem_u hlinks_u hsuf_u
  have hwf₁ : Memory.WellFormed w s₁ := by
    rw [hs₁_eq]; exact wellFormed_clientState hwf hv_u
  have hinfo₁ : ∀ t ∈ pre ++ suf, s₁.mem (nodeBase + 12 * t.rootId) = t.ckey ∧ 0 < t.rootId ∧
      nodeBase + 12 * t.rootId + 11 < s₁.frontier := by
    intro t ht
    have h0 := hinfo t (by
      simp only [List.mem_append, List.mem_cons] at ht ⊢
      rcases ht with h1 | h2
      · exact Or.inl (Or.inl h1)
      · exact Or.inr h2)
    have hck : s₁.mem (nodeBase + 12 * t.rootId) = s.mem (nodeBase + 12 * t.rootId) := by
      by_contra hdiff
      rcases hmem_u _ hdiff with ⟨r0, _, heq⟩ | ⟨u, _, heq⟩ <;> omega
    exact ⟨hck.trans h0.1, h0.2.1, by rw [hfr_u]; exact h0.2.2⟩
  have hnd₁ : ((pre ++ suf).map SHTree.rootId).Nodup := by
    have hsub : ((pre ++ suf).map SHTree.rootId).Sublist
        ((pre ++ [x] ++ suf).map SHTree.rootId) := by
      simp only [List.append_assoc, List.singleton_append, List.map_append, List.map_cons]
      exact (List.Sublist.refl _).append (List.Sublist.cons _ (List.Sublist.refl _))
    exact hsub.nodup hnd
  have hupd := updateSuffixMinUp_spec h16 hwf₁ hlinks_u hsuf_u hinfo₁ hnd₁ hfuel
  rcases hupd with ⟨hv_s, hsafe_s, hm_s, hfr_s, hmem_s, hrep_s⟩
  obtain ⟨s₂, hs₂_eq⟩ : ∃ s₂, s₂ = (Memory.spec 0).clientState s₁
      (updateSuffixMinUp ![nodeBase, pre.getLast?.elim 0 SHTree.rootId, fuel]) := ⟨_, rfl⟩
  rw [← hs₂_eq] at hfr_s hmem_s hrep_s
  have hv : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s
        (extractUnlinkLeaf ![nodeBase, (pre ++ [x] ++ suf).head?.elim 0 SHTree.rootId,
          x.rootId, fuel])) := by
    dsimp only [extractUnlinkLeaf]; simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one,
                                      Matrix.cons_val]
    refine validHistory_bind_step hv_u ?_
    rw [hres_u, ← hs₁_eq]
    exact validHistory_bind_step hv_s (validHistory_pure w _ _)
  have hsafe : extractUnlinkLeafSafe w
      ![nodeBase, (pre ++ [x] ++ suf).head?.elim 0 SHTree.rootId, x.rootId, fuel] s := by
    dsimp only [extractUnlinkLeafSafe]
    simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    refine ⟨h16, ?_⟩
    rw [hres_u, ← hs₁_eq]
    exact hsafe_s
  have hm : memoryCost (extractUnlinkLeaf
      ![nodeBase, (pre ++ [x] ++ suf).head?.elim 0 SHTree.rootId, x.rootId, fuel]) s ≤
      4 + 6 * pre.length := by
    dsimp only [extractUnlinkLeaf]; simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one,
                                      Matrix.cons_val]
    rw [memoryCost_bind', hres_u, ← hs₁_eq, memoryCost_bind', memoryCost_pure, add_zero]
    dsimp only
    omega
  have hres : (Memory.spec 0).clientResult s (extractUnlinkLeaf
      ![nodeBase, (pre ++ [x] ++ suf).head?.elim 0 SHTree.rootId, x.rootId, fuel]) =
      (pre ++ suf).head?.elim 0 SHTree.rootId := by
    dsimp only [extractUnlinkLeaf]; simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one,
                                      Matrix.cons_val]
    rw [StateTransitionSpec.clientResult_bind, hres_u, ← hs₁_eq,
      StateTransitionSpec.clientResult_bind]
    rfl
  have hs_eq : (Memory.spec 0).clientState s (extractUnlinkLeaf
      ![nodeBase, (pre ++ [x] ++ suf).head?.elim 0 SHTree.rootId, x.rootId, fuel]) = s₂ := by
    dsimp only [extractUnlinkLeaf]; simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one,
                                      Matrix.cons_val]
    rw [StateTransitionSpec.clientState_bind, hres_u, ← hs₁_eq,
      StateTransitionSpec.clientState_bind, ← hs₂_eq]
    rfl
  refine ⟨hv, hsafe, hm, hres, ?_, ?_, ?_⟩
  · rw [hs_eq]; exact hfr_s.trans hfr_u
  · intro a ha
    rw [hs_eq] at ha
    by_cases h21 : s₂.mem a = s₁.mem a
    · rw [h21] at ha
      rcases hmem_u _ ha with ⟨r0, hr0, rfl⟩ | ⟨u, hu, rfl⟩
      · exact ⟨r0, List.mem_append_right _ (List.mem_of_head? hr0), 9, Or.inl rfl, rfl⟩
      · exact ⟨u, List.mem_append_left _ (List.mem_of_getLast? hu), 10,
          Or.inr (Or.inl rfl), rfl⟩
    · rcases hmem_s a h21 with ⟨t, ht, rfl⟩
      exact ⟨t, List.mem_append_left _ ht, 11, Or.inr (Or.inr rfl), rfl⟩
  · rw [hs_eq]; exact hrep_s

private theorem extractFixup_noDefill_post
    {w ic₀ nc₀ maxItems maxNodes fuel xId xRank xCk : ℕ}
    {it₀ : SHItem} {restIt : List SHItem} {xLeft xRight : Option SHTree}
    {h : SHHandle} {pre suf : List SHTree} {created : ℕ → ℕ} {s s₁ : Memory.State}
    (h16 : Fits w 16)
    (hinv₀ : SHInv w ic₀ nc₀ maxItems maxNodes h
      (pre ++ [.node xId xRank xCk (it₀ :: restIt) xLeft xRight] ++ suf) created s)
    (hfr₁ : s₁.frontier = s.frontier) (hwf₁ : Memory.WellFormed w s₁)
    (hmem₁_frame : ∀ a, s₁.mem a ≠ s.mem a →
      a = h.nodeBase + 12 * xId + 3 ∨ a = h.nodeBase + 12 * xId + 4 ∨
      a = h.nodeBase + 12 * xId + 5)
    (hother_mem₁ : ∀ t ∈ pre ++ suf, TreeMemRep h.rankThreshold h.itemBase h.nodeBase s₁.mem t)
    (hrl₁ : RootListRep h.nodeBase s₁.mem 0
      (pre ++ [.node xId xRank xCk (it₀ :: restIt) xLeft xRight] ++ suf))
    (hxPop_val : (SHTree.node xId xRank xCk restIt xLeft xRight).Valid h.rankThreshold 0)
    (hxPop_mem : TreeMemRep h.rankThreshold h.itemBase h.nodeBase s₁.mem
      (.node xId xRank xCk restIt xLeft xRight))
    (hv : (Memory.spec w).ValidHistory s₁
      ((Memory.spec w).clientHistory s₁
        (extractFixup ![h.itemBase, h.nodeBase, h.firstRoot, xId, fuel])))
    (hsafe : extractFixupSafe w
      ![h.itemBase, h.nodeBase, h.firstRoot, xId, fuel] s₁)
    (hres : (Memory.spec 0).clientResult s₁
      (extractFixup ![h.itemBase, h.nodeBase, h.firstRoot, xId, fuel]) = h.firstRoot)
    (hs_eq : (Memory.spec 0).clientState s₁
      (extractFixup ![h.itemBase, h.nodeBase, h.firstRoot, xId, fuel]) = s₁)
    (hm_cost : (memoryCost
      (extractFixup ![h.itemBase, h.nodeBase, h.firstRoot, xId, fuel]) s₁ : ℚ) +
      totalPhi h.rankThreshold (pre ++ [.node xId xRank xCk restIt xLeft xRight] ++ suf) ≤
        totalPhi h.rankThreshold
          (pre ++ [.node xId xRank xCk (it₀ :: restIt) xLeft xRight] ++ suf) + 70) :
    let xPop : SHTree := .node xId xRank xCk restIt xLeft xRight
    let d : Fin 5 → ℕ := ![h.itemBase, h.nodeBase, h.firstRoot, xId, fuel]
    (Memory.spec w).ValidHistory s₁ ((Memory.spec w).clientHistory s₁ (extractFixup d)) ∧
    extractFixupSafe w d s₁ ∧
    let nf := (Memory.spec 0).clientResult s₁ (extractFixup d)
    let s₂ := (Memory.spec 0).clientState s₁ (extractFixup d)
    s₂.frontier = s₁.frontier ∧
    (∀ a, s₂.mem a ≠ s₁.mem a → InSHPool ic₀ nc₀ maxItems maxNodes h a) ∧
    ∃ roots',
      SHInv w ic₀ nc₀ maxItems maxNodes
        ⟨h.itemBase, h.nodeBase, nf, h.itemCount, h.nodeCount, h.rankThreshold⟩
        roots' created s₂ ∧
      (forestItems roots').Perm (forestItems (pre ++ [xPop] ++ suf)) ∧
      (∀ p ∈ forestEntries roots',
        ∃ c₀, (p.1, c₀) ∈ forestEntries (pre ++ [xPop] ++ suf) ∧ c₀ ≤ p.2) ∧
      (memoryCost (extractFixup d) s₁ : ℚ) + totalPhi h.rankThreshold roots' ≤
        totalPhi h.rankThreshold
          (pre ++ [.node xId xRank xCk (it₀ :: restIt) xLeft xRight] ++ suf) + 70 := by
  let x : SHTree := .node xId xRank xCk (it₀ :: restIt) xLeft xRight
  let xPop : SHTree := .node xId xRank xCk restIt xLeft xRight
  have hx_in : x ∈ pre ++ [x] ++ suf := by simp [x]
  have hnd_ids : forestNodeIds (pre ++ [xPop] ++ suf) =
      forestNodeIds (pre ++ [x] ++ suf) := by
    simp [forestNodeIds, xPop, x, SHTree.nodeIds_node]
  have hsub_pop : (forestItemIds (pre ++ [xPop] ++ suf)).Sublist
      (forestItemIds (pre ++ [x] ++ suf)) := by
    simp only [forestItemIds, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      SHTree.itemIds_node, xPop, x, List.append_nil, List.map_cons]
    exact ((List.Sublist.refl _).append ((List.Sublist.cons _ (List.Sublist.refl _)).append
      (List.Sublist.refl _))).append (List.Sublist.refl _)
  have hid_sub : ∀ id ∈ forestItemIds (pre ++ [xPop] ++ suf),
      id ∈ forestItemIds (pre ++ [x] ++ suf) := fun _ h => hsub_pop.mem h
  have hid_nodup : (forestItemIds (pre ++ [xPop] ++ suf)).Nodup :=
    hsub_pop.nodup hinv₀.itemIds_nodup
  have hcrk_eq : ∀ k, ((pre ++ [xPop] ++ suf).map (SHTree.countRank k)).sum =
      ((pre ++ [x] ++ suf).map (SHTree.countRank k)).sum := by
    intro k
    simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append,
      List.sum_cons, List.sum_nil, xPop, x, SHTree.countRank_node]
  have hinv₂ : SHInv w ic₀ nc₀ maxItems maxNodes h (pre ++ [xPop] ++ suf) created s₁ := by
    refine ⟨h16, hwf₁, hinv₀.ic_le, hinv₀.ic_max, hinv₀.nc_le, hinv₀.nc_max,
      hinv₀.pool_cap, ?_, hfr₁ ▸ hinv₀.item_pool_lt, hfr₁ ▸ hinv₀.node_pool_lt,
      hinv₀.pools_disj, hinv₀.fits_fuel, ?_, ?_, hid_nodup,
      fun id hid => hinv₀.itemIds_range id (hid_sub id hid), ?_, ?_, ?_, ?_, ?_,
      hinv₀.created_zero, ?_, ?_, ?_⟩
    · have := hinv₀.nc_roots_le; simp only [List.length_append] at this ⊢; omega
    · rw [hnd_ids]; exact hinv₀.nodeIds_nodup
    · rw [hnd_ids]; exact hinv₀.nodeIds_range
    · intro idx h1 h2 hnot
      rw [hnd_ids] at hnot
      have hne_x : idx ≠ xId := fun he =>
        hnot (mem_forestNodeIds hx_in (he ▸ x.rootId_mem_nodeIds))
      have h10 : s₁.mem (h.nodeBase + 12 * idx + 4) = s.mem (h.nodeBase + 12 * idx + 4) := by
        by_contra hdiff
        rcases hmem₁_frame _ hdiff with heq | heq | heq <;> omega
      rw [h10, hinv₀.dead_nodes_empty idx h1 h2 hnot]
    · intro t ht
      rcases List.mem_append.mp ht with hpx | hs
      · rcases List.mem_append.mp hpx with hp | hx1
        · exact hinv₀.trees_valid t (List.mem_append_left _ (List.mem_append_left _ hp))
        · rw [List.mem_singleton.mp hx1]; exact hxPop_val
      · exact hinv₀.trees_valid t (List.mem_append_right _ hs)
    · intro t ht
      rcases List.mem_append.mp ht with hpx | hs
      · rcases List.mem_append.mp hpx with hp | hx1
        · exact hother_mem₁ t (List.mem_append_left _ hp)
        · rw [List.mem_singleton.mp hx1]; exact hxPop_mem
      · exact hother_mem₁ t (List.mem_append_right _ hs)
    · exact RootListRep.replace_mid (x := x) (x' := xPop) rfl rfl rfl hrl₁
    · rw [hinv₀.firstRoot_eq]; cases pre <;> rfl
    · intro k
      have hc := hinv₀.created_step k
      have hmid : [xPop].countP (fun t => decide (t.rank = k)) =
          [x].countP (fun t => decide (t.rank = k)) := rfl
      have hcnt : (pre ++ [xPop] ++ suf).countP (fun t => decide (t.rank = k)) =
          (pre ++ [x] ++ suf).countP (fun t => decide (t.rank = k)) := by
        simp only [List.countP_append, hmid]
      dsimp only [x] at hcnt
      omega
    · intro k
      rw [hcrk_eq k]; exact hinv₀.live_rank_le k
    · intro t ht
      rcases List.mem_append.mp ht with hpx | hs
      · rcases List.mem_append.mp hpx with hp | hx1
        · exact hinv₀.rank_le t (List.mem_append_left _ (List.mem_append_left _ hp))
        · rw [List.mem_singleton.mp hx1]; exact hinv₀.rank_le x hx_in
      · exact hinv₀.rank_le t (List.mem_append_right _ hs)
  refine ⟨hv, hsafe, ?_, ?_, pre ++ [xPop] ++ suf, ?_, .refl _, fun p hp => ⟨p.2, hp, le_rfl⟩,
    hm_cost⟩
  · rw [hs_eq]
  · intro a ha; rw [hs_eq] at ha; exact absurd rfl ha
  · have hnd_h : (⟨h.itemBase, h.nodeBase, h.firstRoot, h.itemCount, h.nodeCount,
        h.rankThreshold⟩ : SHHandle) = h := by cases h; rfl
    rw [hres, hs_eq, hnd_h]; exact hinv₂

private theorem extractFixup_spec {w ic₀ nc₀ maxItems maxNodes fuel xId xRank xCk : ℕ}
    {it₀ : SHItem} {restIt : List SHItem} {xLeft xRight : Option SHTree}
    {h : SHHandle} {pre suf : List SHTree} {created : ℕ → ℕ} {s s₁ : Memory.State}
    (hinv₀ : SHInv w ic₀ nc₀ maxItems maxNodes h
      (pre ++ [.node xId xRank xCk (it₀ :: restIt) xLeft xRight] ++ suf) created s)
    (hfr₁ : s₁.frontier = s.frontier)
    (hwf₁ : Memory.WellFormed w s₁)
    (hmem₁_frame : ∀ a, s₁.mem a ≠ s.mem a →
      a = h.nodeBase + 12 * xId + 3 ∨ a = h.nodeBase + 12 * xId + 4 ∨
      a = h.nodeBase + 12 * xId + 5)
    (hxPop_mem : TreeMemRep h.rankThreshold h.itemBase h.nodeBase s₁.mem
      (.node xId xRank xCk restIt xLeft xRight))
    (hxPop_head_nil : restIt = [] → s₁.mem (h.nodeBase + 12 * xId + 4) = 0)
    (hfuel_ge : shFuelBound h.rankThreshold maxItems ≤ fuel) (hf_fit : Fits w fuel) :
    let x : SHTree := .node xId xRank xCk (it₀ :: restIt) xLeft xRight
    let xPop : SHTree := .node xId xRank xCk restIt xLeft xRight
    let d : Fin 5 → ℕ := ![h.itemBase, h.nodeBase, h.firstRoot, xId, fuel]
    (Memory.spec w).ValidHistory s₁ ((Memory.spec w).clientHistory s₁ (extractFixup d)) ∧
    extractFixupSafe w d s₁ ∧
    let nf := (Memory.spec 0).clientResult s₁ (extractFixup d)
    let s₂ := (Memory.spec 0).clientState s₁ (extractFixup d)
    s₂.frontier = s₁.frontier ∧
    (∀ a, s₂.mem a ≠ s₁.mem a → InSHPool ic₀ nc₀ maxItems maxNodes h a) ∧
    ∃ roots',
      SHInv w ic₀ nc₀ maxItems maxNodes
        ⟨h.itemBase, h.nodeBase, nf, h.itemCount, h.nodeCount, h.rankThreshold⟩
        roots' created s₂ ∧
      (forestItems roots').Perm (forestItems (pre ++ [xPop] ++ suf)) ∧
      (∀ p ∈ forestEntries roots',
        ∃ c₀, (p.1, c₀) ∈ forestEntries (pre ++ [xPop] ++ suf) ∧ c₀ ≤ p.2) ∧
      (memoryCost (extractFixup d) s₁ : ℚ) + totalPhi h.rankThreshold roots' ≤
        totalPhi h.rankThreshold (pre ++ [x] ++ suf) + 70 := by
  let x : SHTree := .node xId xRank xCk (it₀ :: restIt) xLeft xRight
  let xPop : SHTree := .node xId xRank xCk restIt xLeft xRight
  have h16 := hinv₀.fits16
  have hx_in : x ∈ pre ++ [x] ++ suf := by simp [x]
  have hx_val := hinv₀.trees_valid x hx_in
  have hx_mem := hinv₀.trees_mem x hx_in
  have hx_id_pos : 0 < xId := by
    have := (hinv₀.nodeIds_range xId (mem_forestNodeIds hx_in (by simp [x]))).1
    omega
  have hx_id_le : xId ≤ h.nodeCount :=
    (hinv₀.nodeIds_range xId (mem_forestNodeIds hx_in (by simp [x]))).2
  have hx_lt : h.nodeBase + 12 * xId + 11 < s₁.frontier := by
    have := hinv₀.nc_max; have := hinv₀.node_pool_lt; rw [hfr₁]; omega
  have hxl_eq : s₁.mem (h.nodeBase + 12 * xId + 6) = xLeft.elim 0 SHTree.rootId :=
    hxPop_mem.left_eq
  have hxr_eq : s₁.mem (h.nodeBase + 12 * xId + 7) = xRight.elim 0 SHTree.rootId :=
    hxPop_mem.right_eq
  have hsz_eq : s₁.mem (h.nodeBase + 12 * xId + 3) = restIt.length := hxPop_mem.size_eq
  have htgt_eq : s₁.mem (h.nodeBase + 12 * xId + 2) = targetSize h.rankThreshold xRank :=
    hxPop_mem.target_eq
  have hxl_zero_iff : xLeft.elim 0 SHTree.rootId = 0 ↔ xLeft = none := by
    cases xLeft with
    | none => simp
    | some c =>
      have hc := (hxPop_mem.left_mem c rfl).rootId_ne
      simp [hc]
  have hxr_zero_iff : xRight.elim 0 SHTree.rootId = 0 ↔ xRight = none := by
    cases xRight with
    | none => simp
    | some c =>
      have hc := (hxPop_mem.right_mem c rfl).rootId_ne
      simp [hc]
  have hother_mem₁ : ∀ t ∈ pre ++ suf,
      TreeMemRep h.rankThreshold h.itemBase h.nodeBase s₁.mem t := by
    intro t ht
    have ht_in : t ∈ pre ++ [x] ++ suf := by
      simp only [List.mem_append] at ht ⊢
      rcases ht with h1 | h2
      · exact Or.inl (Or.inl h1)
      · exact Or.inr h2
    refine TreeMemRep.congr (fun id hid j hj => ?_) (fun it hit k hk => ?_)
      (hinv₀.trees_mem t ht_in)
    · symm; by_contra hdiff
      have hne : id ≠ xId := by
        intro heq
        subst heq
        have hd := hinv₀.nodeIds_nodup
        simp only [forestNodeIds, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
          List.append_nil] at hd
        rcases List.mem_append.mp ht with hp | hs
        · have hdisj := (list_nodup_append_disj hd).1
          have hp_in : id ∈ forestNodeIds pre := mem_forestNodeIds hp hid
          exact (list_nodup_append_disj hdisj).2.2 id hp_in x.rootId_mem_nodeIds
        · have hs_in : id ∈ forestNodeIds suf := mem_forestNodeIds hs hid
          exact (list_nodup_append_disj hd).2.2 id
            (List.mem_append_right _ x.rootId_mem_nodeIds) hs_in
      rcases hmem₁_frame _ hdiff with h3 | h4 | h5 <;> omega
    · symm; by_contra hdiff
      have hit_le := (hinv₀.itemIds_range it.id (mem_forestItemIds ht_in hit)).2
      have := hinv₀.ic_max; have := hinv₀.nc_max
      rcases hmem₁_frame _ hdiff with heq | heq | heq
      · exact hinv₀.pools_disj_node_item (nid := xId) (iid := it.id) (j := 3)
          (by omega) (by omega) (by decide) hk heq.symm
      · exact hinv₀.pools_disj_node_item (nid := xId) (iid := it.id) (j := 4)
          (by omega) (by omega) (by decide) hk heq.symm
      · exact hinv₀.pools_disj_node_item (nid := xId) (iid := it.id) (j := 5)
          (by omega) (by omega) (by decide) hk heq.symm
  have hrl₁ : RootListRep h.nodeBase s₁.mem 0 (pre ++ [x] ++ suf) := by
    refine RootListRep.congr (fun t ht j hj => ?_) hinv₀.rootList
    symm; by_contra hdiff
    rcases hmem₁_frame _ hdiff with heq | heq | heq <;> rcases hj with rfl | rfl | rfl <;> omega
  have hnd_roots : ((pre ++ [x] ++ suf).map SHTree.rootId).Nodup := by
    have hsub : ((pre ++ [x] ++ suf).map SHTree.rootId).Sublist
        (forestNodeIds (pre ++ [x] ++ suf)) := by
      simp only [forestNodeIds]
      induction (pre ++ [x] ++ suf) with
      | nil => simp
      | cons a l ih =>
        simp only [List.map_cons, List.flatMap_cons]
        cases a with
        | node aid _ _ _ al ar =>
          rw [SHTree.nodeIds_node, SHTree.rootId]
          exact List.Sublist.cons_cons aid (List.Sublist.trans ih (List.sublist_append_right _ _))
    exact hsub.nodup hinv₀.nodeIds_nodup
  have hinfo₁ : ∀ t ∈ pre ++ [x] ++ suf, s₁.mem (h.nodeBase + 12 * t.rootId) = t.ckey ∧
      0 < t.rootId ∧ h.nodeBase + 12 * t.rootId + 11 < s₁.frontier := by
    intro t ht
    have ht_ck : s₁.mem (h.nodeBase + 12 * t.rootId) = t.ckey := by
      rcases List.mem_append.mp ht with hpx | hs
      · rcases List.mem_append.mp hpx with hp | hx1
        · exact (hother_mem₁ t (List.mem_append_left _ hp)).ckey_eq
        · rw [List.mem_singleton.mp hx1]; exact hxPop_mem.ckey_eq
      · exact (hother_mem₁ t (List.mem_append_right _ hs)).ckey_eq
    have hrng := hinv₀.nodeIds_range t.rootId (mem_forestNodeIds ht t.rootId_mem_nodeIds)
    have := hinv₀.nc_max; have := hinv₀.node_pool_lt; rw [hfr₁]
    exact ⟨ht_ck, by omega, by omega⟩
  have hrest_sz_fit : Fits w (restIt.length + restIt.length) := by
    have hle : restIt.length ≤ maxItems := by
      have hid_nd : xPop.itemIds.Nodup := by
        have hsub : xPop.itemIds.Sublist x.itemIds := by
          simp only [xPop, x, SHTree.itemIds_node, List.map_cons]
          exact (List.Sublist.cons _ (List.Sublist.refl _)).append (List.Sublist.refl _)
        exact (hsub.trans (itemIds_sub_mid pre x suf)).nodup hinv₀.itemIds_nodup
      have hit_nd : (xPop.itemIds.map (fun id => id - (ic₀ + 1))).Nodup := by
        refine List.Nodup.map_on ?_ hid_nd
        intro a ha b hb _
        have hax := itemIds_sub_mid pre x suf |>.mem (xPop_itemIds_sub ha)
        have hbx := itemIds_sub_mid pre x suf |>.mem (xPop_itemIds_sub hb)
        have := (hinv₀.itemIds_range a hax).1
        have := (hinv₀.itemIds_range b hbx).1
        omega
      have hlen_xpop : xPop.itemIds.length ≤ maxItems := by
        rw [← List.length_map (f := fun id => id - (ic₀ + 1))]
        refine List.length_le_of_nodup_lt hit_nd ?_
        intro y hy
        rcases List.mem_map.mp hy with ⟨id, hid, rfl⟩
        have hidx := itemIds_sub_mid pre x suf |>.mem (xPop_itemIds_sub hid)
        have := hinv₀.itemIds_range id hidx
        have := hinv₀.ic_max
        omega
      simp only [xPop, SHTree.itemIds_node, List.length_append, List.length_map] at hlen_xpop
      omega
    have hsb : 2 * (maxItems + 1) ≤ shFuelBound h.rankThreshold maxItems :=
      Nat.mul_le_mul_right _ (by omega)
    exact hinv₀.fits_fuel.of_le (by omega)
  by_cases hleaf : xLeft = none ∧ xRight = none
  · rcases hleaf with ⟨rfl, rfl⟩
    by_cases hnil : restIt = []
    · subst hnil
      have hpre_fuel : pre.length ≤ fuel := by
        have hpw := hrl₁.pairwise_rank
        have hp_le := rootList_pre_length_le_rank hpw
        have hxr := hinv₀.rank_le x hx_in
        have hle_fuel : 100 * (maxItems + 1) ≤ shFuelBound h.rankThreshold maxItems :=
          Nat.mul_le_mul_right _ (by omega)
        have := hinv₀.nc_roots_le; have := hinv₀.ic_max; have := hinv₀.ic_le; omega
      have hun := extractUnlinkLeaf_spec h16 hwf₁ hrl₁ hinfo₁ hnd_roots hpre_fuel
      rcases hun with ⟨hv_u, hsafe_u, hm_u, hres_u, hfr_u, hmem_u, hrep_u⟩
      have hrt_x : x.rootId = xId := rfl
      rw [hrt_x, ← hinv₀.firstRoot_eq] at hv_u hsafe_u hm_u hres_u hfr_u hmem_u hrep_u
      obtain ⟨s₂, hs₂_eq⟩ : ∃ s₂, s₂ = (Memory.spec 0).clientState s₁
          (extractUnlinkLeaf ![h.nodeBase, h.firstRoot, xId, fuel]) := ⟨_, rfl⟩
      rw [← hs₂_eq] at hfr_u hmem_u hrep_u
      have hwf₂ : Memory.WellFormed w s₂ := by
        rw [hs₂_eq]; exact wellFormed_clientState hwf₁ hv_u
      have hv : (Memory.spec w).ValidHistory s₁
          ((Memory.spec w).clientHistory s₁
            (extractFixup ![h.itemBase, h.nodeBase, h.firstRoot, xId, fuel])) := by
        dsimp only [extractFixup]; simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one,
                                     Matrix.cons_val]
        refine validHistory_read_bind (by omega) (validHistory_read_bind (by omega) ?_)
        refine validHistory_read_bind (by omega) (validHistory_read_bind (by omega) ?_)
        rw [hxl_eq, hxr_eq, hsz_eq]
        simp only [Option.elim_none, List.length_nil, and_self, ↓reduceIte]
        exact hv_u
      have hsafe : extractFixupSafe w
          ![h.itemBase, h.nodeBase, h.firstRoot, xId, fuel] s₁ := by
        dsimp only [extractFixupSafe]; simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one,
                                         Matrix.cons_val]
        rw [hxl_eq, hxr_eq, hsz_eq]
        simp only [Option.elim_none, List.length_nil]
        exact ⟨h16, fun h => by simp at h, fun _ _ => hsafe_u, fun h => by simp at h⟩
      have hm : memoryCost (extractFixup ![h.itemBase, h.nodeBase, h.firstRoot, xId, fuel]) s₁ ≤
          8 + 6 * pre.length := by
        dsimp only [extractFixup]; simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one,
                                     Matrix.cons_val]
        repeat (rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read])
        rw [hxl_eq, hxr_eq, hsz_eq]
        simp only [Option.elim_none, List.length_nil, and_self, ↓reduceIte]
        omega
      have hres : (Memory.spec 0).clientResult s₁
          (extractFixup ![h.itemBase, h.nodeBase, h.firstRoot, xId, fuel]) =
          (pre ++ suf).head?.elim 0 SHTree.rootId := by
        dsimp only [extractFixup]; simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one,
                                     Matrix.cons_val]
        repeat rw [clientResult_bind_read]
        rw [hxl_eq, hxr_eq, hsz_eq]
        simp only [Option.elim_none, List.length_nil, and_self, ↓reduceIte]
        exact hres_u
      have hs_eq : (Memory.spec 0).clientState s₁
          (extractFixup ![h.itemBase, h.nodeBase, h.firstRoot, xId, fuel]) = s₂ := by
        dsimp only [extractFixup]; simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one,
                                     Matrix.cons_val]
        repeat rw [clientState_bind_read]
        rw [hxl_eq, hxr_eq, hsz_eq]
        simp only [Option.elim_none, List.length_nil, and_self, ↓reduceIte, ← hs₂_eq]
      have htrees₂ : ∀ t ∈ pre ++ suf,
          TreeMemRep h.rankThreshold h.itemBase h.nodeBase s₂.mem t := by
        intro t ht
        refine TreeMemRep.congr (fun id hid j hj => ?_) (fun it hit k hk => ?_)
          (hother_mem₁ t ht)
        · symm; by_contra hdiff
          rcases hmem_u _ hdiff with ⟨u, hu, j', _, heq⟩; omega
        · symm; by_contra hdiff
          have ht_in : t ∈ pre ++ [x] ++ suf := by
            rcases List.mem_append.mp ht with h1 | h2
            · exact List.mem_append_left _ (List.mem_append_left _ h1)
            · exact List.mem_append_right _ h2
          have hit_le := (hinv₀.itemIds_range it.id (mem_forestItemIds ht_in hit)).2
          have := hinv₀.ic_max
          rcases hmem_u _ hdiff with ⟨u, hu, j', hj', heq⟩
          have hu_in : u ∈ pre ++ [x] ++ suf := by
            rcases List.mem_append.mp hu with h1 | h2
            · exact List.mem_append_left _ (List.mem_append_left _ h1)
            · exact List.mem_append_right _ h2
          have := (hinv₀.nodeIds_range u.rootId
            (mem_forestNodeIds hu_in u.rootId_mem_nodeIds)).2
          have := hinv₀.nc_max
          exact hinv₀.pools_disj_node_item (nid := u.rootId) (iid := it.id) (j := j')
            (by omega) (by omega) (by rcases hj' with rfl | rfl | rfl <;> decide) hk heq.symm
      have hnd₂ : (forestNodeIds (pre ++ suf)).Nodup := by
        have hsub : (forestNodeIds (pre ++ suf)).Sublist
            (forestNodeIds (pre ++ [x] ++ suf)) := by
          simp only [forestNodeIds, List.flatMap_append]
          exact (List.sublist_append_left _ _).append (List.Sublist.refl _)
        exact hsub.nodup hinv₀.nodeIds_nodup
      have hid₂ : (forestItemIds (pre ++ suf)).Nodup := by
        have hsub : (forestItemIds (pre ++ suf)).Sublist
            (forestItemIds (pre ++ [x] ++ suf)) := by
          simp only [forestItemIds, List.flatMap_append]
          exact (List.sublist_append_left _ _).append (List.Sublist.refl _)
        exact hsub.nodup hinv₀.itemIds_nodup
      have hinv₂ : SHInv w ic₀ nc₀ maxItems maxNodes
          ⟨h.itemBase, h.nodeBase, (pre ++ suf).head?.elim 0 SHTree.rootId,
            h.itemCount, h.nodeCount, h.rankThreshold⟩ (pre ++ suf) created s₂ := by
        refine ⟨h16, hwf₂, hinv₀.ic_le, hinv₀.ic_max, hinv₀.nc_le, hinv₀.nc_max,
          hinv₀.pool_cap, ?_, hfr_u ▸ hfr₁ ▸ hinv₀.item_pool_lt,
          hfr_u ▸ hfr₁ ▸ hinv₀.node_pool_lt, hinv₀.pools_disj, hinv₀.fits_fuel,
          hnd₂, ?_, hid₂, ?_, ?_, ?_, htrees₂, hrep_u, rfl, hinv₀.created_zero, ?_, ?_, ?_⟩
        · have := hinv₀.nc_roots_le; simp only [List.length_append] at this ⊢; omega
        · intro id hid
          apply hinv₀.nodeIds_range id
          simp only [forestNodeIds, List.flatMap_append, List.mem_append] at hid ⊢
          rcases hid with h1 | h2
          · exact Or.inl (Or.inl h1)
          · exact Or.inr h2
        · intro id hid
          apply hinv₀.itemIds_range id
          simp only [forestItemIds, List.flatMap_append, List.mem_append] at hid ⊢
          rcases hid with h1 | h2
          · exact Or.inl (Or.inl h1)
          · exact Or.inr h2
        · intro idx h1 h2 hnot
          by_cases hx_eq : idx = xId
          · subst hx_eq
            have h21 : s₂.mem (h.nodeBase + 12 * idx + 4) =
                s₁.mem (h.nodeBase + 12 * idx + 4) := by
              by_contra hdiff
              rcases hmem_u _ hdiff with ⟨u, _, j, hj, heq⟩
              rcases hj with rfl | rfl | rfl <;> omega
            rw [h21, hxPop_head_nil rfl]
          · have h_not_old : idx ∉ forestNodeIds (pre ++ [x] ++ suf) := by
              intro hold
              simp only [forestNodeIds, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
                List.append_nil, List.mem_append] at hold
              rcases hold with (h1 | h2) | h3
              · exact hnot (by simp [forestNodeIds, h1])
              · simp only [x, SHTree.nodeIds_node, Option.elim_none, List.append_nil,
                  List.mem_singleton] at h2
                exact hx_eq h2
              · exact hnot (by simp [forestNodeIds, h3])
            have hs0 := hinv₀.dead_nodes_empty idx h1 h2 h_not_old
            have h10 : s₁.mem (h.nodeBase + 12 * idx + 4) =
                s.mem (h.nodeBase + 12 * idx + 4) := by
              by_contra hdiff
              rcases hmem₁_frame _ hdiff with heq | heq | heq <;> omega
            have h21 : s₂.mem (h.nodeBase + 12 * idx + 4) =
                s₁.mem (h.nodeBase + 12 * idx + 4) := by
              by_contra hdiff
              rcases hmem_u _ hdiff with ⟨u, _, j, hj, heq⟩
              rcases hj with rfl | rfl | rfl <;> omega
            rw [h21, h10, hs0]
        · intro t ht
          apply hinv₀.trees_valid t
          rcases List.mem_append.mp ht with h1 | h2
          · exact List.mem_append_left _ (List.mem_append_left _ h1)
          · exact List.mem_append_right _ h2
        · intro k
          have hc := hinv₀.created_step k
          simp only [List.countP_append, List.countP_cons, List.countP_nil] at hc ⊢
          omega
        · intro k
          have hl := hinv₀.live_rank_le k
          simp only [List.map_append, List.sum_append] at hl ⊢
          omega
        · intro t ht
          apply hinv₀.rank_le t
          rcases List.mem_append.mp ht with h1 | h2
          · exact List.mem_append_left _ (List.mem_append_left _ h1)
          · exact List.mem_append_right _ h2
      refine ⟨hv, hsafe, ?_, ?_, pre ++ suf, ?_, ?_, ?_, ?_⟩
      · rw [hs_eq]; exact hfr_u
      · intro a ha; rw [hs_eq] at ha
        rcases hmem_u a ha with ⟨u, hu, j, hj, rfl⟩
        have hu_in : u ∈ pre ++ [x] ++ suf := by
          rcases List.mem_append.mp hu with h1 | h2
          · exact List.mem_append_left _ (List.mem_append_left _ h1)
          · exact List.mem_append_right _ h2
        have hrng := hinv₀.nodeIds_range u.rootId
          (mem_forestNodeIds hu_in u.rootId_mem_nodeIds)
        have := hinv₀.nc_max
        right; rcases hj with rfl | rfl | rfl <;> omega
      · rw [hres, hs_eq]; exact hinv₂
      · simp [forestItems, forestEntries]
      · intro p hp; exact ⟨p.2, by simpa [forestEntries, xPop] using hp, le_rfl⟩
      · have hm_q : (memoryCost (extractFixup
            ![h.itemBase, h.nodeBase, h.firstRoot, xId, fuel]) s₁ : ℚ) ≤
            8 + 6 * (pre.length : ℚ) := by
          exact_mod_cast hm
        have hpw := hrl₁.pairwise_rank
        have hpre_le : (pre.length : ℚ) ≤ (xRank : ℚ) := by
          exact_mod_cast (rootList_pre_length_le_rank hpw)
        have hx_phi : 30 ≤ x.phi h.rankThreshold := by
          have h1 : 0 ≤ x.itemPhiSum h.rankThreshold := x.itemPhiSum_nonneg h.rankThreshold
          have hnc : x.nodeCount = 1 := by simp [x, SHTree.nodeCount_node]
          have hphi : x.phi h.rankThreshold =
              120 * x.itemPhiSum h.rankThreshold + 30 * (x.nodeCount : ℚ) := rfl
          rw [hphi, hnc]
          norm_num
          linarith
        have hpop_nn : 0 ≤ popDeficit h.rankThreshold x := popDeficit_nonneg h.rankThreshold x
        have hx_phi_s : 30 ≤ (SHTree.node xId xRank xCk [it₀] none none).phi h.rankThreshold :=
          hx_phi
        have hpop_s : 0 ≤ popDeficit h.rankThreshold
            (SHTree.node xId xRank xCk [it₀] none none) := hpop_nn
        have hrc_s :
            rootCredit (SHTree.node xId xRank xCk [it₀] none none).rank = 86 + 6 * (xRank : ℚ) :=
          rfl
        simp only [totalPhi_append]
        rw [totalPhi_cons, totalPhi_nil, add_zero, hrc_s]
        linarith
    · have hlen_pos : restIt.length ≠ 0 := Nat.ne_of_gt (List.length_pos_of_ne_nil hnil)
      have hv : (Memory.spec w).ValidHistory s₁
          ((Memory.spec w).clientHistory s₁
            (extractFixup ![h.itemBase, h.nodeBase, h.firstRoot, xId, fuel])) := by
        dsimp only [extractFixup]; simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one,
                                     Matrix.cons_val]
        refine validHistory_read_bind (by omega) (validHistory_read_bind (by omega) ?_)
        refine validHistory_read_bind (by omega) (validHistory_read_bind (by omega) ?_)
        rw [hxl_eq, hxr_eq, hsz_eq]
        simp only [Option.elim_none, and_self, hlen_pos, ↓reduceIte]
        exact validHistory_pure w _ _
      have hsafe : extractFixupSafe w
          ![h.itemBase, h.nodeBase, h.firstRoot, xId, fuel] s₁ := by
        dsimp only [extractFixupSafe]; simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one,
                                         Matrix.cons_val]
        rw [hxl_eq, hxr_eq, hsz_eq]
        simp only [Option.elim_none]
        exact ⟨h16, fun h => by simp at h, fun _ h0 => absurd h0 hlen_pos, fun h => by simp at h⟩
      have hm : memoryCost (extractFixup ![h.itemBase, h.nodeBase, h.firstRoot, xId, fuel]) s₁ =
          4 := by
        dsimp only [extractFixup]; simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one,
                                     Matrix.cons_val]
        repeat (rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read])
        rw [hxl_eq, hxr_eq, hsz_eq]
        simp only [Option.elim_none, and_self, hlen_pos, ↓reduceIte, memoryCost_pure]
      have hres : (Memory.spec 0).clientResult s₁
          (extractFixup ![h.itemBase, h.nodeBase, h.firstRoot, xId, fuel]) = h.firstRoot := by
        dsimp only [extractFixup]; simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one,
                                     Matrix.cons_val]
        repeat rw [clientResult_bind_read]
        rw [hxl_eq, hxr_eq, hsz_eq]
        simp only [Option.elim_none, and_self, hlen_pos, ↓reduceIte]
        rfl
      have hs_eq : (Memory.spec 0).clientState s₁
          (extractFixup ![h.itemBase, h.nodeBase, h.firstRoot, xId, fuel]) = s₁ := by
        dsimp only [extractFixup]; simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one,
                                     Matrix.cons_val]
        repeat rw [clientState_bind_read]
        rw [hxl_eq, hxr_eq, hsz_eq]
        simp only [Option.elim_none, and_self, hlen_pos, ↓reduceIte]
        rfl
      have hxPop_val : xPop.Valid h.rankThreshold 0 := by
        dsimp only [x] at hx_val
        rcases hx_val with ⟨_, hcap, hlb, hok, hk8, _, _, _, _, _⟩
        exact .node hnil (by rw [List.length_cons] at hcap; omega) hlb
          (fun it hit => hok it (List.mem_cons_of_mem _ hit))
          (fun hr it hit => hk8 hr it (List.mem_cons_of_mem _ hit))
          (fun h => by cases h with | inl h1 => cases h1 | inr h2 => cases h2)
          (fun _ hc => by cases hc) (fun _ hc => by cases hc)
          (fun _ hc => by cases hc) (fun _ hc => by cases hc)
      refine extractFixup_noDefill_post h16 hinv₀ hfr₁ hwf₁ hmem₁_frame hother_mem₁ hrl₁
        hxPop_val hxPop_mem hv hsafe hres hs_eq ?_
      rw [hm]
      push_cast
      have hx_phi : xPop.phi h.rankThreshold ≤
          (SHTree.node xId xRank xCk (it₀ :: restIt) none none).phi h.rankThreshold := by
        simp only [SHTree.phi, SHTree.itemPhiSum_node, SHTree.nodeCount_node,
          xPop, Option.elim_none, List.length_cons, Nat.cast_add, Nat.cast_one]
        have := itemPhi_nonneg h.rankThreshold xRank
        linarith
      have hpop0 : popDeficit h.rankThreshold xPop = 0 := rfl
      have hrc_eq : rootCredit xPop.rank =
          rootCredit (SHTree.node xId xRank xCk (it₀ :: restIt) none none).rank := rfl
      have hpop_nn :
          0 ≤ popDeficit h.rankThreshold (SHTree.node xId xRank xCk (it₀ :: restIt) none none) :=
        popDeficit_nonneg h.rankThreshold _
      simp only [totalPhi_append, totalPhi_cons, totalPhi_nil, add_zero]
      rw [hpop0, hrc_eq]
      linarith
  · have hnonleaf : xLeft.isSome ∨ xRight.isSome := by
      cases xLeft <;> cases xRight
      · exact absurd ⟨rfl, rfl⟩ hleaf
      · exact Or.inr rfl
      · exact Or.inl rfl
      · exact Or.inl rfl
    have hnl_rw : ¬ (xLeft.elim 0 SHTree.rootId = 0 ∧ xRight.elim 0 SHTree.rootId = 0) := by
      rw [hxl_zero_iff, hxr_zero_iff]; exact hleaf
    by_cases hlt_tgt : restIt.length + restIt.length < targetSize h.rankThreshold xRank
    · have hnd_xp : xPop.nodeIds.Nodup := by
        have hsub : xPop.nodeIds.Sublist x.nodeIds := by
          simp only [xPop, x, SHTree.nodeIds_node]
          exact List.Sublist.refl _
        exact (hsub.trans (nodeIds_sub_mid pre x suf)).nodup hinv₀.nodeIds_nodup
      have hid_xp : xPop.itemIds.Nodup := by
        have hsub : xPop.itemIds.Sublist (forestItemIds (pre ++ [x] ++ suf)) := by
          refine List.Sublist.trans ?_ (itemIds_sub_mid pre x suf)
          simp only [xPop, x, SHTree.itemIds_node, List.map_cons]
          exact (List.Sublist.cons _ (List.Sublist.refl _)).append (List.Sublist.refl _)
        exact hsub.nodup hinv₀.itemIds_nodup
      have hxp_nd_in : ∀ id ∈ xPop.nodeIds,
          nc₀ < id ∧ id ≤ nc₀ + 2 * (maxItems - ic₀) := by
        intro id hid
        have hid_x : id ∈ x.nodeIds := by
          simp only [xPop, x, SHTree.nodeIds_node] at hid ⊢; exact hid
        have := hinv₀.nodeIds_range id (mem_forestNodeIds hx_in hid_x)
        have := hinv₀.nc_roots_le; have := hinv₀.nc_le
        have := hinv₀.ic_max; omega
      have hxp_id_in : ∀ id ∈ xPop.itemIds, ic₀ < id ∧ id ≤ maxItems := by
        intro id hid
        have hid_x : id ∈ x.itemIds := xPop_itemIds_sub hid
        have := hinv₀.itemIds_range id ((itemIds_sub_mid pre x suf).mem hid_x)
        have := hinv₀.ic_max; omega
      have hxp_nlt : ∀ id ∈ xPop.nodeIds, h.nodeBase + 12 * id + 11 < s₁.frontier := by
        intro id hid
        have := (hxp_nd_in id hid).2; have := hinv₀.pool_cap; have := hinv₀.node_pool_lt
        rw [hfr₁]; omega
      have hxp_ilt : ∀ it ∈ xPop.allItems, h.itemBase + 3 * it.id + 2 < s₁.frontier := by
        intro it hit
        have := (hxp_id_in it.id (List.mem_map_of_mem hit)).2
        have := hinv₀.item_pool_lt; rw [hfr₁]; omega
      have hxp_disj : ∀ id ∈ xPop.nodeIds, ∀ it ∈ xPop.allItems, ∀ j < 12, ∀ k < 3,
          h.nodeBase + 12 * id + j ≠ h.itemBase + 3 * it.id + k := by
        intro id hid it hit j hj k hk
        have := (hxp_nd_in id hid).2; have := hinv₀.pool_cap
        have := (hxp_id_in it.id (List.mem_map_of_mem hit)).2
        exact hinv₀.pools_disj_node_item (nid := id) (iid := it.id)
          (by omega) (by omega) hj hk
      have hxp_val : ZipCurValid h.rankThreshold 0 xPop := by
        dsimp only [x] at hx_val
        rcases hx_val with ⟨_, hcap, hlb, hok, hk8, _, hlr, hlv, hrr, hrv⟩
        exact ⟨by
          dsimp only [xPop, SHTree.items, SHTree.rank]
          rw [List.length_cons] at hcap; omega,
          hlb,
          fun it hit => hok it (List.mem_cons_of_mem _ hit),
          fun hr it hit => hk8 hr it (List.mem_cons_of_mem _ hit),
          fun _ => hnonleaf,
          fun c hc => ⟨hlr c hc, hlv c hc⟩,
          fun c hc => ⟨hrr c hc, hrv c hc⟩⟩
      have hxp_fuel : xPop.phi h.rankThreshold + 5 ≤ 5 * (fuel : ℚ) := by
        have hle := tree_phi_le_fuel (rt := h.rankThreshold) hid_xp hxp_id_in hnd_xp hxp_nd_in
        have hfq : ((shFuelBound h.rankThreshold maxItems : ℕ) : ℚ) ≤ (fuel : ℚ) := by
          exact_mod_cast hfuel_ge
        linarith
      have hdef := defill_spec h16 hwf₁ hxp_val hnd_xp hid_xp hxPop_mem hxp_nlt hxp_ilt
        hxp_disj hf_fit hxp_fuel
      rcases hdef with ⟨hv_def, hsafe_def, hfr_def, hmem_def, x', hx'_rt, hx'_rk, hx'_val,
        hx'_pop, _, hx'_nd, hx'_sub, hx'_dead, hx'_crk, hx'_perm, hx'_ck_mono, hx'_mem, hx'_phi⟩
      have hxpop_rt : xPop.rootId = xId := rfl
      have hxpop_rk : xPop.rank = xRank := rfl
      rw [hxpop_rt] at hv_def hsafe_def hfr_def hmem_def hx'_rt hx'_dead hx'_mem hx'_phi
      rw [hxpop_rk] at hx'_rk
      obtain ⟨s_def, hs_def_eq⟩ : ∃ s_def, s_def = (Memory.spec 0).clientState s₁
          (defill ![h.itemBase, h.nodeBase, xId, fuel]) := ⟨_, rfl⟩
      rw [← hs_def_eq] at hfr_def hmem_def hx'_dead hx'_mem
      have hwf_def : Memory.WellFormed w s_def := by
        rw [hs_def_eq]; exact wellFormed_clientState hwf₁ hv_def
      have hpre_links_def : RootListLinksOnly h.nodeBase s_def.mem 0 suf (pre ++ [x']) := by
        rw [List.append_assoc] at hrl₁
        obtain ⟨hpl, hxr⟩ := RootListRep.split_append hrl₁
        rcases hxr with ⟨hx_lt_suf, hx9, hx10, _, _⟩
        rw [List.singleton_append] at hpl
        have hdisj_x_pre : ∀ t ∈ pre, ∀ j, j = 9 ∨ j = 10 →
            s_def.mem (h.nodeBase + 12 * t.rootId + j) =
              s₁.mem (h.nodeBase + 12 * t.rootId + j) := by
          intro t ht j hj
          by_contra hdiff
          rcases hmem_def _ hdiff with ⟨id, hid, j', hj', heq⟩ | ⟨it, hit, heq⟩
          · have hid_x : id ∈ x.nodeIds := by
              simp only [xPop, x, SHTree.nodeIds_node] at hid ⊢; exact hid
            have hne : t.rootId ≠ id := by
              have hd := hinv₀.nodeIds_nodup
              simp only [forestNodeIds, List.flatMap_append, List.flatMap_cons,
                List.flatMap_nil, List.append_nil] at hd
              exact fun he => (list_nodup_append_disj (list_nodup_append_disj hd).1).2.2
                t.rootId (mem_forestNodeIds ht t.rootId_mem_nodeIds) (he ▸ hid_x)
            rcases hj with rfl | rfl <;> omega
          · have hit_le := (hxp_id_in it.id (List.mem_map_of_mem hit)).2
            have ht_le := (hinv₀.nodeIds_range t.rootId
              (mem_forestNodeIds (List.mem_append_left _ (List.mem_append_left _ ht))
                t.rootId_mem_nodeIds)).2
            have := hinv₀.nc_max
            rcases hj with rfl | rfl
            · exact hinv₀.pools_disj_node_item (nid := t.rootId) (iid := it.id) (j := 9) (k := 2)
                (by omega) (by omega) (by decide) (by decide) heq
            · exact hinv₀.pools_disj_node_item (nid := t.rootId) (iid := it.id) (j := 10) (k := 2)
                (by omega) (by omega) (by decide) (by decide) heq
        rw [rootListLinksOnly_snoc]
        refine ⟨rootListLinksOnly_congr (fun t ht j hj => (hdisj_x_pre t ht j hj).symm)
          (RootListLinksOnly.replace_head (x := x) hx'_rt hx'_rk hpl), ?_, ?_, ?_⟩
        · intro u hu; rw [hx'_rk]; exact hx_lt_suf u hu
        · rw [hx'_rt]
          have hnot : s_def.mem (h.nodeBase + 12 * xId + 9) =
              s₁.mem (h.nodeBase + 12 * xId + 9) := by
            by_contra hdiff
            rcases hmem_def _ hdiff with ⟨id, _, j', hj', heq⟩ | ⟨it, hit, heq⟩
            · omega
            · have hid_le := (hxp_id_in it.id (List.mem_map_of_mem hit)).2
              have := hinv₀.nc_max
              exact hinv₀.pools_disj_node_item (nid := xId) (iid := it.id) (j := 9) (k := 2)
                (by omega) (by omega) (by decide) (by decide) heq
          rw [hnot]; exact hx9
        · rw [hx'_rt]
          have hnot : s_def.mem (h.nodeBase + 12 * xId + 10) =
              s₁.mem (h.nodeBase + 12 * xId + 10) := by
            by_contra hdiff
            rcases hmem_def _ hdiff with ⟨id, _, j', hj', heq⟩ | ⟨it, hit, heq⟩
            · omega
            · have hid_le := (hxp_id_in it.id (List.mem_map_of_mem hit)).2
              have := hinv₀.nc_max
              exact hinv₀.pools_disj_node_item (nid := xId) (iid := it.id) (j := 10) (k := 2)
                (by omega) (by omega) (by decide) (by decide) heq
          rw [hnot]; exact hx10
      have hsuf_rep_def : RootListRep h.nodeBase s_def.mem
          ((pre ++ [x']).getLast?.elim 0 SHTree.rootId) suf := by
        rw [List.append_assoc] at hrl₁
        have hsuf₁ := (RootListRep.split_append hrl₁).2.2.2.2.2
        have hlast : (pre ++ [x']).getLast?.elim 0 SHTree.rootId = xId := by
          simp [List.getLast?_append, hx'_rt]
        rw [hlast]
        refine RootListRep.congr (fun t ht j hj => ?_) hsuf₁
        symm; by_contra hdiff
        rcases hmem_def _ hdiff with ⟨id, _, j', hj', heq⟩ | ⟨it, hit, heq⟩
        · rcases hj with rfl | rfl | rfl <;> omega
        · have hid_le := (hxp_id_in it.id (List.mem_map_of_mem hit)).2
          have ht_le := (hinv₀.nodeIds_range t.rootId
            (mem_forestNodeIds (List.mem_append_right _ ht) t.rootId_mem_nodeIds)).2
          have := hinv₀.nc_max
          rcases hj with rfl | rfl | rfl
          · exact hinv₀.pools_disj_node_item (nid := t.rootId) (iid := it.id) (j := 9) (k := 2)
              (by omega) (by omega) (by decide) (by decide) heq
          · exact hinv₀.pools_disj_node_item (nid := t.rootId) (iid := it.id) (j := 10) (k := 2)
              (by omega) (by omega) (by decide) (by decide) heq
          · exact hinv₀.pools_disj_node_item (nid := t.rootId) (iid := it.id) (j := 11) (k := 2)
              (by omega) (by omega) (by decide) (by decide) heq
      have hinfo_def : ∀ t ∈ (pre ++ [x']) ++ suf,
          s_def.mem (h.nodeBase + 12 * t.rootId) = t.ckey ∧ 0 < t.rootId ∧
          h.nodeBase + 12 * t.rootId + 11 < s_def.frontier := by
        intro t ht
        rw [List.append_assoc] at ht
        rcases List.mem_append.mp ht with hp | hxs
        · have ht_old := hinfo₁ t (List.mem_append_left _ (List.mem_append_left _ hp))
          have hagree : s_def.mem (h.nodeBase + 12 * t.rootId) =
              s₁.mem (h.nodeBase + 12 * t.rootId) := by
            by_contra hdiff
            rcases hmem_def _ hdiff with ⟨id, hid, j', hj', heq⟩ | ⟨it, hit, heq⟩
            · have hid_x : id ∈ x.nodeIds := by
                simp only [xPop, x, SHTree.nodeIds_node] at hid ⊢; exact hid
              have hne : t.rootId ≠ id := by
                have hd := hinv₀.nodeIds_nodup
                simp only [forestNodeIds, List.flatMap_append] at hd
                have h1 := (list_nodup_append_disj hd).1
                exact fun he => (list_nodup_append_disj h1).2.2 t.rootId
                  (mem_forestNodeIds hp t.rootId_mem_nodeIds)
                  (show t.rootId ∈ [x].flatMap SHTree.nodeIds from
                    List.mem_append_left _ (he ▸ hid_x))
              omega
            · have hit_le := (hxp_id_in it.id (List.mem_map_of_mem hit)).2
              have ht_le := (hinv₀.nodeIds_range t.rootId
                (mem_forestNodeIds (List.mem_append_left _ (List.mem_append_left _ hp))
                  t.rootId_mem_nodeIds)).2
              have := hinv₀.nc_max
              exact hinv₀.pools_disj_node_item (nid := t.rootId) (iid := it.id) (j := 0) (k := 2)
                (by omega) (by omega) (by decide) (by decide) heq
          exact ⟨hagree.trans ht_old.1, ht_old.2.1, by rw [hfr_def]; exact ht_old.2.2⟩
        · rcases List.mem_cons.mp hxs with rfl | hs
          · refine ⟨hx'_mem.ckey_eq, by rw [hx'_rt]; exact hx_id_pos,
              by rw [hx'_rt, hfr_def]; exact hx_lt⟩
          · have ht_old := hinfo₁ t (List.mem_append_right _ hs)
            have hagree : s_def.mem (h.nodeBase + 12 * t.rootId) =
                s₁.mem (h.nodeBase + 12 * t.rootId) := by
              by_contra hdiff
              rcases hmem_def _ hdiff with ⟨id, hid, j', hj', heq⟩ | ⟨it, hit, heq⟩
              · have hid_x : id ∈ x.nodeIds := by
                  simp only [xPop, x, SHTree.nodeIds_node] at hid ⊢; exact hid
                have hne : t.rootId ≠ id := by
                  have hd := hinv₀.nodeIds_nodup
                  simp only [forestNodeIds, List.flatMap_append, List.flatMap_cons] at hd
                  exact fun he => (list_nodup_append_disj hd).2.2 id
                    (List.mem_append_right _ (List.mem_append_left _ hid_x))
                    (he ▸ mem_forestNodeIds hs t.rootId_mem_nodeIds)
                omega
              · have hit_le := (hxp_id_in it.id (List.mem_map_of_mem hit)).2
                have ht_le := (hinv₀.nodeIds_range t.rootId
                  (mem_forestNodeIds (List.mem_append_right _ hs) t.rootId_mem_nodeIds)).2
                have := hinv₀.nc_max
                exact hinv₀.pools_disj_node_item (nid := t.rootId) (iid := it.id) (j := 0) (k := 2)
                  (by omega) (by omega) (by decide) (by decide) heq
            exact ⟨hagree.trans ht_old.1, ht_old.2.1, by rw [hfr_def]; exact ht_old.2.2⟩
      have hnd_def : (((pre ++ [x']) ++ suf).map SHTree.rootId).Nodup := by
        have hmap_eq : ((pre ++ [x']) ++ suf).map SHTree.rootId =
            ((pre ++ [x]) ++ suf).map SHTree.rootId := by
          simp only [List.append_assoc, List.map_append, List.map_cons, hx'_rt]; rfl
        rw [hmap_eq]; exact hnd_roots
      have hfuel_upd : (pre ++ [x']).length ≤ fuel := by
        have hp_le := rootList_pre_length_le_rank hrl₁.pairwise_rank
        have hxr := hinv₀.rank_le x hx_in
        have hle_fuel : 100 * (maxItems + 1) ≤ shFuelBound h.rankThreshold maxItems :=
          Nat.mul_le_mul_right _ (by omega)
        have := hinv₀.nc_roots_le; have := hinv₀.nc_le
        have := hinv₀.ic_max; have := hinv₀.ic_le
        simp only [List.length_append, List.length_singleton]; omega
      have hupd := updateSuffixMinUp_spec h16 hwf_def hpre_links_def hsuf_rep_def hinfo_def
        hnd_def hfuel_upd
      rcases hupd with ⟨hv_u, hsafe_u, hm_u, hfr_u, hmem_u, hrep_u⟩
      have hlast_eq : (pre ++ [x']).getLast?.elim 0 SHTree.rootId = xId := by
        simp [List.getLast?_append, hx'_rt]
      rw [hlast_eq] at hv_u hsafe_u hm_u hfr_u hmem_u hrep_u
      obtain ⟨s₂, hs₂_eq⟩ : ∃ s₂, s₂ = (Memory.spec 0).clientState s_def
          (updateSuffixMinUp ![h.nodeBase, xId, fuel]) := ⟨_, rfl⟩
      rw [← hs₂_eq] at hfr_u hmem_u hrep_u
      have hwf₂ : Memory.WellFormed w s₂ := by
        rw [hs₂_eq]; exact wellFormed_clientState hwf_def hv_u
      have hv : (Memory.spec w).ValidHistory s₁
          ((Memory.spec w).clientHistory s₁
            (extractFixup ![h.itemBase, h.nodeBase, h.firstRoot, xId, fuel])) := by
        dsimp only [extractFixup]; simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one,
                                     Matrix.cons_val]
        refine validHistory_read_bind (by omega) (validHistory_read_bind (by omega) ?_)
        refine validHistory_read_bind (by omega) (validHistory_read_bind (by omega) ?_)
        rw [hxl_eq, hxr_eq, hsz_eq, htgt_eq]
        simp only [hnl_rw, hlt_tgt, ↓reduceIte]
        refine validHistory_bind_step hv_def ?_
        rw [← hs_def_eq]
        exact validHistory_bind_step hv_u (validHistory_pure w _ _)
      have hsafe : extractFixupSafe w
          ![h.itemBase, h.nodeBase, h.firstRoot, xId, fuel] s₁ := by
        dsimp only [extractFixupSafe]; simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one,
                                         Matrix.cons_val]
        rw [hxl_eq, hxr_eq, hsz_eq, htgt_eq]
        refine ⟨h16, fun _ => hrest_sz_fit, fun h => absurd h hnl_rw, fun _ _ => ⟨?_, ?_⟩⟩
        · exact hsafe_def
        · rw [← hs_def_eq]; exact hsafe_u
      have hm : memoryCost (extractFixup ![h.itemBase, h.nodeBase, h.firstRoot, xId, fuel]) s₁ =
          4 + memoryCost (defill ![h.itemBase, h.nodeBase, xId, fuel]) s₁ +
            memoryCost (updateSuffixMinUp ![h.nodeBase, xId, fuel]) s_def := by
        dsimp only [extractFixup]; simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one,
                                     Matrix.cons_val]
        repeat (rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read])
        rw [hxl_eq, hxr_eq, hsz_eq, htgt_eq]
        simp only [hnl_rw, hlt_tgt, ↓reduceIte, memoryCost_bind', ← hs_def_eq,
          memoryCost_pure, add_zero]
        omega
      have hres : (Memory.spec 0).clientResult s₁
          (extractFixup ![h.itemBase, h.nodeBase, h.firstRoot, xId, fuel]) = h.firstRoot := by
        dsimp only [extractFixup]; simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one,
                                     Matrix.cons_val]
        repeat rw [clientResult_bind_read]
        rw [hxl_eq, hxr_eq, hsz_eq, htgt_eq]
        simp only [hnl_rw, hlt_tgt, ↓reduceIte, StateTransitionSpec.clientResult_bind]
        rfl
      have hs_eq : (Memory.spec 0).clientState s₁
          (extractFixup ![h.itemBase, h.nodeBase, h.firstRoot, xId, fuel]) = s₂ := by
        dsimp only [extractFixup]; simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one,
                                     Matrix.cons_val]
        repeat rw [clientState_bind_read]
        rw [hxl_eq, hxr_eq, hsz_eq, htgt_eq]
        simp only [hnl_rw, hlt_tgt, ↓reduceIte]
        rw [StateTransitionSpec.clientState_bind, ← hs_def_eq,
          StateTransitionSpec.clientState_bind, ← hs₂_eq]
        rfl
      have hx'_mem₂ : TreeMemRep h.rankThreshold h.itemBase h.nodeBase s₂.mem x' := by
        refine TreeMemRep.congr (fun id hid j hj => ?_) (fun it hit k hk => ?_) hx'_mem
        · symm; by_contra hdiff
          rcases hmem_u _ hdiff with ⟨t, _, heq⟩; omega
        · symm; by_contra hdiff
          rcases hmem_u _ hdiff with ⟨t, ht, heq⟩
          have ht_old : t.rootId ∈ forestNodeIds (pre ++ [x] ++ suf) := by
            rcases List.mem_append.mp ht with hp | hx'mem
            · exact mem_forestNodeIds (List.mem_append_left _ (List.mem_append_left _ hp))
                t.rootId_mem_nodeIds
            · rw [List.mem_singleton.mp hx'mem, hx'_rt]
              exact mem_forestNodeIds hx_in x.rootId_mem_nodeIds
          have hid_le := (hinv₀.nodeIds_range t.rootId ht_old).2
          have hit_p : it ∈ xPop.allItems := hx'_perm.mem_iff.mp hit
          have hit_le := (hxp_id_in it.id (List.mem_map_of_mem hit_p)).2
          have := hinv₀.nc_max
          exact hinv₀.pools_disj_node_item (nid := t.rootId) (iid := it.id) (j := 11)
            (by omega) (by omega) (by decide) hk heq.symm
      have hother_mem₂ : ∀ t ∈ pre ++ suf,
          TreeMemRep h.rankThreshold h.itemBase h.nodeBase s₂.mem t := by
        intro t ht
        refine TreeMemRep.congr (fun id hid j hj => ?_) (fun it hit k hk => ?_)
          (hother_mem₁ t ht)
        · have h2d : s₂.mem (h.nodeBase + 12 * id + j) =
              s_def.mem (h.nodeBase + 12 * id + j) := by
            by_contra hdiff
            rcases hmem_u _ hdiff with ⟨u, _, heq⟩; omega
          have hd1 : s_def.mem (h.nodeBase + 12 * id + j) =
              s₁.mem (h.nodeBase + 12 * id + j) := by
            by_contra hdiff
            rcases hmem_def _ hdiff with ⟨idp, hidp, j', hj', heq⟩ | ⟨itp, hitp, heq⟩
            · have hidp_x : idp ∈ x.nodeIds := by
                simpa [xPop, x, SHTree.nodeIds_node] using hidp
              have hne : id ≠ idp := by
                have hd := hinv₀.nodeIds_nodup
                simp only [forestNodeIds, List.flatMap_append, List.flatMap_cons,
                  List.flatMap_nil, List.append_nil] at hd
                rcases List.mem_append.mp ht with hp | hs
                · exact fun he => (list_nodup_append_disj (list_nodup_append_disj hd).1).2.2 id
                    (mem_forestNodeIds hp hid) (he ▸ hidp_x)
                · exact fun he => (list_nodup_append_disj hd).2.2 id
                    (List.mem_append_right _ (he ▸ hidp_x))
                    (mem_forestNodeIds hs hid)
              omega
            · have hit_le := (hxp_id_in itp.id (List.mem_map_of_mem hitp)).2
              have ht_in : t ∈ pre ++ [x] ++ suf := by
                rcases List.mem_append.mp ht with hp | hs
                · exact List.mem_append_left _ (List.mem_append_left _ hp)
                · exact List.mem_append_right _ hs
              have hid_le := (hinv₀.nodeIds_range id (mem_forestNodeIds ht_in hid)).2
              have := hinv₀.nc_max
              exact hinv₀.pools_disj_node_item (nid := id) (iid := itp.id) (k := 2)
                (by omega) (by omega) (by omega) (by decide) heq
          exact (h2d.trans hd1).symm
        · have h2d : s₂.mem (h.itemBase + 3 * it.id + k) =
              s_def.mem (h.itemBase + 3 * it.id + k) := by
            by_contra hdiff
            rcases hmem_u _ hdiff with ⟨u, hu, heq⟩
            have hu_old : u.rootId ∈ forestNodeIds (pre ++ [x] ++ suf) := by
              rcases List.mem_append.mp hu with hp | hx'm
              · exact mem_forestNodeIds (List.mem_append_left _ (List.mem_append_left _ hp))
                  u.rootId_mem_nodeIds
              · rw [List.mem_singleton.mp hx'm, hx'_rt]
                exact mem_forestNodeIds hx_in x.rootId_mem_nodeIds
            have ht_in : t ∈ pre ++ [x] ++ suf := by
              rcases List.mem_append.mp ht with hp | hs
              · exact List.mem_append_left _ (List.mem_append_left _ hp)
              · exact List.mem_append_right _ hs
            have hit_le := (hinv₀.itemIds_range it.id (mem_forestItemIds ht_in hit)).2
            have hu_le := (hinv₀.nodeIds_range u.rootId hu_old).2
            have := hinv₀.nc_max; have := hinv₀.ic_max
            exact hinv₀.pools_disj_node_item (nid := u.rootId) (iid := it.id) (j := 11)
              (by omega) (by omega) (by decide) hk heq.symm
          have hd1 : s_def.mem (h.itemBase + 3 * it.id + k) =
              s₁.mem (h.itemBase + 3 * it.id + k) := by
            by_contra hdiff
            have ht_in : t ∈ pre ++ [x] ++ suf := by
              rcases List.mem_append.mp ht with hp | hs
              · exact List.mem_append_left _ (List.mem_append_left _ hp)
              · exact List.mem_append_right _ hs
            have hit_le := (hinv₀.itemIds_range it.id (mem_forestItemIds ht_in hit)).2
            rcases hmem_def _ hdiff with ⟨idp, hidp, j', hj', heq⟩ | ⟨itp, hitp, heq⟩
            · have hidp_x : idp ∈ x.nodeIds := by
                simpa [xPop, x, SHTree.nodeIds_node] using hidp
              have hidp_le := (hinv₀.nodeIds_range idp (mem_forestNodeIds hx_in hidp_x)).2
              have := hinv₀.nc_max; have := hinv₀.ic_max
              exact hinv₀.pools_disj_node_item (nid := idp) (iid := it.id) (j := j')
                (by omega) (by omega) (by omega) hk heq.symm
            · have hne : it.id ≠ itp.id := by
                have hd := hinv₀.itemIds_nodup
                have hitp_x : itp.id ∈ x.itemIds := xPop_itemIds_sub (List.mem_map_of_mem hitp)
                simp only [forestItemIds, List.flatMap_append, List.flatMap_cons,
                  List.flatMap_nil, List.append_nil] at hd
                rcases List.mem_append.mp ht with hp | hs
                · exact fun he => (list_nodup_append_disj (list_nodup_append_disj hd).1).2.2 it.id
                    (mem_forestItemIds hp hit) (he ▸ hitp_x)
                · exact fun he => (list_nodup_append_disj hd).2.2 it.id
                    (List.mem_append_right _ (he ▸ hitp_x))
                    (mem_forestItemIds hs hit)
              omega
          exact (h2d.trans hd1).symm
      have hnd₂ : (forestNodeIds ((pre ++ [x']) ++ suf)).Nodup := by
        simp only [forestNodeIds, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
          List.append_nil]
        have hd := hinv₀.nodeIds_nodup
        simp only [forestNodeIds, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
          List.append_nil] at hd
        have hd1 := (list_nodup_append_disj hd).1
        refine List.nodup_append.mpr ⟨List.nodup_append.mpr
          ⟨(list_nodup_append_disj hd1).1, hx'_nd, ?_⟩,
          (list_nodup_append_disj hd).2.1, ?_⟩
        · intro a ha b hb rfl
          have hbx : a ∈ x.nodeIds := by
            simpa [xPop, x, SHTree.nodeIds_node] using hx'_sub a hb
          exact (list_nodup_append_disj hd1).2.2 a ha hbx
        · intro a ha b hb rfl
          rcases List.mem_append.mp ha with ha1 | ha2
          · exact (list_nodup_append_disj hd).2.2 a (List.mem_append_left _ ha1) hb
          · have hax : a ∈ x.nodeIds := by
              simpa [xPop, x, SHTree.nodeIds_node] using hx'_sub a ha2
            exact (list_nodup_append_disj hd).2.2 a (List.mem_append_right _ hax) hb
      have hid₂ : (forestItemIds ((pre ++ [x']) ++ suf)).Nodup := by
        simp only [forestItemIds, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
          List.append_nil]
        have hd := hinv₀.itemIds_nodup
        simp only [forestItemIds, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
          List.append_nil] at hd
        have hd1 := (list_nodup_append_disj hd).1
        have hx'_id_p : x'.itemIds.Perm xPop.itemIds := hx'_perm.map SHItem.id
        refine List.nodup_append.mpr ⟨List.nodup_append.mpr
          ⟨(list_nodup_append_disj hd1).1, hx'_id_p.nodup_iff.mpr hid_xp, ?_⟩,
          (list_nodup_append_disj hd).2.1, ?_⟩
        · intro a ha b hb rfl
          have hb_x : a ∈ x.itemIds := xPop_itemIds_sub (hx'_id_p.mem_iff.mp hb)
          exact (list_nodup_append_disj hd1).2.2 a ha hb_x
        · intro a ha b hb rfl
          rcases List.mem_append.mp ha with ha1 | ha2
          · exact (list_nodup_append_disj hd).2.2 a (List.mem_append_left _ ha1) hb
          · have ha_x : a ∈ x.itemIds := xPop_itemIds_sub (hx'_id_p.mem_iff.mp ha2)
            exact (list_nodup_append_disj hd).2.2 a (List.mem_append_right _ ha_x) hb
      have hfirst₂ : h.firstRoot = ((pre ++ [x']) ++ suf).head?.elim 0 SHTree.rootId := by
        rw [hinv₀.firstRoot_eq]
        cases pre with
        | nil => exact hx'_rt.symm
        | cons _ _ => rfl
      have hinv₂ : SHInv w ic₀ nc₀ maxItems maxNodes h ((pre ++ [x']) ++ suf) created s₂ := by
        refine ⟨h16, hwf₂, hinv₀.ic_le, hinv₀.ic_max, hinv₀.nc_le, hinv₀.nc_max,
          hinv₀.pool_cap, ?_, hfr_u ▸ hfr_def ▸ hfr₁ ▸ hinv₀.item_pool_lt,
          hfr_u ▸ hfr_def ▸ hfr₁ ▸ hinv₀.node_pool_lt, hinv₀.pools_disj, hinv₀.fits_fuel,
          hnd₂, ?_, hid₂, ?_, ?_, ?_, ?_, hrep_u, hfirst₂, hinv₀.created_zero, ?_, ?_, ?_⟩
        · have := hinv₀.nc_roots_le; simp only [List.length_append] at this ⊢; omega
        · intro id hid
          simp only [forestNodeIds, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
            List.append_nil, List.mem_append] at hid
          rcases hid with (h1 | h2) | h3
          · apply hinv₀.nodeIds_range id
            simp only [forestNodeIds, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
              List.append_nil, List.mem_append]
            exact Or.inl (Or.inl h1)
          · have hx2 : id ∈ x.nodeIds := by
              simpa [xPop, x, SHTree.nodeIds_node] using hx'_sub id h2
            exact hinv₀.nodeIds_range id (mem_forestNodeIds hx_in hx2)
          · apply hinv₀.nodeIds_range id
            simp only [forestNodeIds, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
              List.append_nil, List.mem_append]
            exact Or.inr h3
        · intro id hid
          simp only [forestItemIds, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
            List.append_nil, List.mem_append] at hid
          rcases hid with (h1 | h2) | h3
          · apply hinv₀.itemIds_range id
            simp only [forestItemIds, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
              List.append_nil, List.mem_append]
            exact Or.inl (Or.inl h1)
          · have hx2 : id ∈ xPop.itemIds := (hx'_perm.map SHItem.id).mem_iff.mp h2
            exact hinv₀.itemIds_range id ((itemIds_sub_mid pre x suf).mem (xPop_itemIds_sub hx2))
          · apply hinv₀.itemIds_range id
            simp only [forestItemIds, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
              List.append_nil, List.mem_append]
            exact Or.inr h3
        · intro idx h1 h2 hnot
          have h2d : s₂.mem (h.nodeBase + 12 * idx + 4) =
              s_def.mem (h.nodeBase + 12 * idx + 4) := by
            by_contra hdiff
            rcases hmem_u _ hdiff with ⟨u, _, heq⟩; omega
          rw [h2d]
          by_cases h_in_xp : idx ∈ xPop.nodeIds
          · have h_not_x' : idx ∉ x'.nodeIds := fun h => by
              apply hnot
              simp only [forestNodeIds, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
                List.append_nil, List.mem_append]
              exact Or.inl (Or.inr h)
            exact hx'_dead idx h_in_xp h_not_x'
          · have h_not_old : idx ∉ forestNodeIds (pre ++ [x] ++ suf) := by
              intro hold
              simp only [forestNodeIds, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
                List.append_nil, List.mem_append] at hold
              rcases hold with (h_p | h_x) | h_s
              · apply hnot
                simp only [forestNodeIds, List.flatMap_append, List.mem_append]
                exact Or.inl (Or.inl h_p)
              · exact h_in_xp (by simpa [xPop, x, SHTree.nodeIds_node] using h_x)
              · apply hnot
                simp only [forestNodeIds, List.flatMap_append, List.mem_append]
                exact Or.inr h_s
            have hs0 := hinv₀.dead_nodes_empty idx h1 h2 h_not_old
            have hd1 : s_def.mem (h.nodeBase + 12 * idx + 4) =
                s₁.mem (h.nodeBase + 12 * idx + 4) := by
              by_contra hdiff
              rcases hmem_def _ hdiff with ⟨idp, hidp, j', hj', heq⟩ | ⟨it, hit, heq⟩
              · have : idx = idp := by omega
                exact h_in_xp (this ▸ hidp)
              · have := (hxp_id_in it.id (List.mem_map_of_mem hit)).2
                have := hinv₀.nc_max
                exact hinv₀.pools_disj_node_item (nid := idx) (iid := it.id) (j := 4) (k := 2)
                  (by omega) (by omega) (by decide) (by decide) heq
            have hne_x : idx ≠ xId := fun he =>
              h_in_xp (he ▸ xPop.rootId_mem_nodeIds)
            have h10 : s₁.mem (h.nodeBase + 12 * idx + 4) =
                s.mem (h.nodeBase + 12 * idx + 4) := by
              by_contra hdiff
              rcases hmem₁_frame _ hdiff with heq | heq | heq <;> omega
            rw [hd1, h10, hs0]
        · intro t ht
          rcases List.mem_append.mp ht with hpx | hs
          · rcases List.mem_append.mp hpx with hp | hx'm
            · exact hinv₀.trees_valid t (List.mem_append_left _ (List.mem_append_left _ hp))
            · rw [List.mem_singleton.mp hx'm]; exact hx'_val
          · exact hinv₀.trees_valid t (List.mem_append_right _ hs)
        · intro t ht
          rcases List.mem_append.mp ht with hpx | hs
          · rcases List.mem_append.mp hpx with hp | hx'm
            · exact hother_mem₂ t (List.mem_append_left _ hp)
            · rw [List.mem_singleton.mp hx'm]; exact hx'_mem₂
          · exact hother_mem₂ t (List.mem_append_right _ hs)
        · intro k
          have hc := hinv₀.created_step k
          have hmid : [x'].countP (fun t => decide (t.rank = k)) =
              [x].countP (fun t => decide (t.rank = k)) := by
            simp only [List.countP_singleton, hx'_rk]; rfl
          have hcnt : ((pre ++ [x']) ++ suf).countP (fun t => decide (t.rank = k)) =
              (pre ++ [x] ++ suf).countP (fun t => decide (t.rank = k)) := by
            simp only [List.countP_append, hmid]
          dsimp only [x] at hcnt
          omega
        · intro k
          have hl := hinv₀.live_rank_le k
          have hck := hx'_crk k
          have hxp_eq : xPop.countRank k =
              (SHTree.node xId xRank xCk (it₀ :: restIt) xLeft xRight).countRank k := by
            simp only [xPop, SHTree.countRank_node]
          simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append,
            List.sum_cons, List.sum_nil, add_zero] at hl ⊢
          omega
        · intro t ht
          rcases List.mem_append.mp ht with hpx | hs
          · rcases List.mem_append.mp hpx with hp | hx'm
            · exact hinv₀.rank_le t (List.mem_append_left _ (List.mem_append_left _ hp))
            · rw [List.mem_singleton.mp hx'm, hx'_rk]; exact hinv₀.rank_le x hx_in
          · exact hinv₀.rank_le t (List.mem_append_right _ hs)
      have hnd_h : (⟨h.itemBase, h.nodeBase, h.firstRoot, h.itemCount, h.nodeCount,
          h.rankThreshold⟩ : SHHandle) = h := by cases h; rfl
      refine ⟨hv, hsafe, ?_, ?_, (pre ++ [x']) ++ suf, ?_, ?_, ?_, ?_⟩
      · rw [hs_eq]; exact hfr_u.trans hfr_def
      · intro a ha; rw [hs_eq] at ha
        by_cases h2d : s₂.mem a = s_def.mem a
        · rw [h2d] at ha
          rcases hmem_def _ ha with ⟨id, hid, j, hj, rfl⟩ | ⟨it, hit, rfl⟩
          · have hid_x : id ∈ x.nodeIds := by simpa [xPop, x, SHTree.nodeIds_node] using hid
            have hrng := hinv₀.nodeIds_range id (mem_forestNodeIds hx_in hid_x)
            have := hinv₀.nc_max
            right; omega
          · have hrng := hxp_id_in it.id (List.mem_map_of_mem hit)
            left; omega
        · rcases hmem_u a h2d with ⟨u, hu, rfl⟩
          have hu_old : u.rootId ∈ forestNodeIds (pre ++ [x] ++ suf) := by
            rcases List.mem_append.mp hu with hp | hx'm
            · exact mem_forestNodeIds (List.mem_append_left _ (List.mem_append_left _ hp))
                u.rootId_mem_nodeIds
            · rw [List.mem_singleton.mp hx'm, hx'_rt]
              exact mem_forestNodeIds hx_in x.rootId_mem_nodeIds
          have hrng := hinv₀.nodeIds_range u.rootId hu_old
          have := hinv₀.nc_max
          right; omega
      · rw [hres, hs_eq, hnd_h]; exact hinv₂
      · simp only [forestItems, forestEntries, List.flatMap_append, List.flatMap_cons,
          List.flatMap_nil, List.append_nil, List.map_append]
        exact ((List.Perm.refl _).append hx'_perm).append (List.Perm.refl _)
      · intro pe hpe
        simp only [forestEntries, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, List.mem_append] at hpe
        rcases hpe with (hp | hx'e) | hs
        · exact ⟨pe.2, by
            simp only [forestEntries, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
              List.append_nil, List.mem_append]
            exact Or.inl (Or.inl hp), le_rfl⟩
        · rcases hx'_ck_mono pe hx'e with ⟨c₀, hc₀, hle⟩
          exact ⟨c₀, by
            simp only [forestEntries, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
              List.append_nil, List.mem_append]
            exact Or.inl (Or.inr hc₀), hle⟩
        · exact ⟨pe.2, by
            simp only [forestEntries, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
              List.append_nil, List.mem_append]
            exact Or.inr hs, le_rfl⟩
      · have hm_u_q : (memoryCost (updateSuffixMinUp ![h.nodeBase, xId, fuel]) s_def : ℚ) ≤
            6 * ((pre.length : ℚ) + 1) := by
          have h1 : (memoryCost (updateSuffixMinUp ![h.nodeBase, xId, fuel]) s_def : ℚ) ≤
              6 * ((pre ++ [x']).length : ℚ) := by exact_mod_cast hm_u
          simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one] at h1
          exact h1
        have hp_le_q : (pre.length : ℚ) ≤ (xRank : ℚ) := by
          exact_mod_cast rootList_pre_length_le_rank hrl₁.pairwise_rank
        have hxp_phi : xPop.phi h.rankThreshold + 120 * (h.rankThreshold : ℚ) ≤
            x.phi h.rankThreshold := by
          simp only [SHTree.phi, SHTree.itemPhiSum_node, SHTree.nodeCount_node,
            xPop, x, List.length_cons, Nat.cast_add, Nat.cast_one]
          have hge := itemPhi_ge_threshold h.rankThreshold xRank
          linarith
        have hcost_upd : 6 * (xRank : ℚ) + 6 ≤
            popDeficit h.rankThreshold x + 6 * (h.rankThreshold : ℚ) + 6 := by
          by_cases hr_le : xRank ≤ h.rankThreshold
          · have hr_q : (xRank : ℚ) ≤ (h.rankThreshold : ℚ) := by exact_mod_cast hr_le
            have hpd := popDeficit_nonneg h.rankThreshold x
            linarith
          · have hr_gt : h.rankThreshold < xRank := by omega
            rcases targetSize_even_of_gt hr_gt with ⟨m, hm2⟩
            have hle2 : 2 * (restIt.length + 1) ≤ targetSize h.rankThreshold xRank := by omega
            have hsub : targetSize h.rankThreshold xRank ≤
                2 * (targetSize h.rankThreshold xRank -
                  min (restIt.length + 1) (targetSize h.rankThreshold xRank)) := by omega
            have hsub_q : (targetSize h.rankThreshold xRank : ℚ) ≤
                2 * ((targetSize h.rankThreshold xRank -
                  min (restIt.length + 1) (targetSize h.rankThreshold xRank) : ℕ) : ℚ) := by
              exact_mod_cast hsub
            have hpop_lb : 6 * (targetSize h.rankThreshold xRank : ℚ) ≤
                popDeficit h.rankThreshold x := by
              dsimp only [popDeficit, x, SHTree.left, SHTree.right, SHTree.rank, SHTree.items]
              simp only [hnonleaf, ↓reduceIte, List.length_cons]
              linarith
            have hr_ts : (xRank : ℚ) ≤
                (targetSize h.rankThreshold xRank : ℚ) + (h.rankThreshold : ℚ) := by
              exact_mod_cast rank_le_targetSize_add h.rankThreshold xRank
            linarith
        have hxp_phi_s : xPop.phi h.rankThreshold + 120 * (h.rankThreshold : ℚ) ≤
            (SHTree.node xId xRank xCk (it₀ :: restIt) xLeft xRight).phi h.rankThreshold :=
          hxp_phi
        have hcost_upd_s : 6 * (xRank : ℚ) + 6 ≤
            popDeficit h.rankThreshold (SHTree.node xId xRank xCk (it₀ :: restIt) xLeft xRight) +
              6 * (h.rankThreshold : ℚ) + 6 := hcost_upd
        have hx'_phi_p :
            (memoryCost (defill ![h.itemBase, h.nodeBase, xId, fuel]) s₁ : ℚ) +
              x'.phi h.rankThreshold ≤ xPop.phi h.rankThreshold + 6 := hx'_phi
        have hpd_nil : popDeficit h.rankThreshold x' = 0 := hx'_pop
        have hrc_eq : rootCredit xRank =
            rootCredit (SHTree.node xId xRank xCk (it₀ :: restIt) xLeft xRight).rank := rfl
        have hrt_nn : (0 : ℚ) ≤ (h.rankThreshold : ℚ) := Nat.cast_nonneg _
        rw [hm]
        push_cast
        simp only [totalPhi_append, totalPhi_cons, totalPhi_nil, add_zero, hx'_rk]
        rw [hpd_nil, hrc_eq]
        linarith
    · have hnil : restIt ≠ [] := by
        intro hne
        have := targetSize_pos h.rankThreshold xRank
        rw [hne, List.length_nil] at hlt_tgt
        omega
      have hxPop_val : xPop.Valid h.rankThreshold 0 := by
        dsimp only [x] at hx_val
        rcases hx_val with ⟨_, hcap, hlb, hok, hk8, _, hlr, hlv, hrr, hrv⟩
        exact .node hnil (by rw [List.length_cons] at hcap; omega) hlb
          (fun it hit => hok it (List.mem_cons_of_mem _ hit))
          (fun hr it hit => hk8 hr it (List.mem_cons_of_mem _ hit))
          (fun _ => by omega) hlr hlv hrr hrv
      have hv : (Memory.spec w).ValidHistory s₁
          ((Memory.spec w).clientHistory s₁
            (extractFixup ![h.itemBase, h.nodeBase, h.firstRoot, xId, fuel])) := by
        dsimp only [extractFixup]; simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one,
                                     Matrix.cons_val]
        refine validHistory_read_bind (by omega) (validHistory_read_bind (by omega) ?_)
        refine validHistory_read_bind (by omega) (validHistory_read_bind (by omega) ?_)
        rw [hxl_eq, hxr_eq, hsz_eq, htgt_eq]
        simp only [hnl_rw, hlt_tgt, ↓reduceIte]
        exact validHistory_pure w _ _
      have hsafe : extractFixupSafe w
          ![h.itemBase, h.nodeBase, h.firstRoot, xId, fuel] s₁ := by
        dsimp only [extractFixupSafe]; simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one,
                                         Matrix.cons_val]
        rw [hxl_eq, hxr_eq, hsz_eq, htgt_eq]
        exact ⟨h16, fun _ => hrest_sz_fit, fun h => absurd h hnl_rw,
          fun _ hc => absurd hc hlt_tgt⟩
      have hm : memoryCost (extractFixup ![h.itemBase, h.nodeBase, h.firstRoot, xId, fuel]) s₁ =
          4 := by
        dsimp only [extractFixup]; simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one,
                                     Matrix.cons_val]
        repeat (rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read])
        rw [hxl_eq, hxr_eq, hsz_eq, htgt_eq]
        simp only [hnl_rw, hlt_tgt, ↓reduceIte, memoryCost_pure]
      have hres : (Memory.spec 0).clientResult s₁
          (extractFixup ![h.itemBase, h.nodeBase, h.firstRoot, xId, fuel]) = h.firstRoot := by
        dsimp only [extractFixup]; simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one,
                                     Matrix.cons_val]
        repeat rw [clientResult_bind_read]
        rw [hxl_eq, hxr_eq, hsz_eq, htgt_eq]
        simp only [hnl_rw, hlt_tgt, ↓reduceIte]
        rfl
      have hs_eq : (Memory.spec 0).clientState s₁
          (extractFixup ![h.itemBase, h.nodeBase, h.firstRoot, xId, fuel]) = s₁ := by
        dsimp only [extractFixup]; simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one,
                                     Matrix.cons_val]
        repeat rw [clientState_bind_read]
        rw [hxl_eq, hxr_eq, hsz_eq, htgt_eq]
        simp only [hnl_rw, hlt_tgt, ↓reduceIte]
        rfl
      refine extractFixup_noDefill_post h16 hinv₀ hfr₁ hwf₁ hmem₁_frame hother_mem₁ hrl₁
        hxPop_val hxPop_mem hv hsafe hres hs_eq ?_
      rw [hm]
      push_cast
      have hx_phi : xPop.phi h.rankThreshold ≤ x.phi h.rankThreshold := by
        simp only [SHTree.phi, SHTree.itemPhiSum_node, SHTree.nodeCount_node,
          xPop, x, List.length_cons, Nat.cast_add, Nat.cast_one]
        have := itemPhi_nonneg h.rankThreshold xRank
        linarith
      have hsub : targetSize h.rankThreshold xRank -
          min restIt.length (targetSize h.rankThreshold xRank) ≤
          (targetSize h.rankThreshold xRank -
            min (restIt.length + 1) (targetSize h.rankThreshold xRank)) + 1 := by omega
      have hsub_q : ((targetSize h.rankThreshold xRank -
          min restIt.length (targetSize h.rankThreshold xRank) : ℕ) : ℚ) ≤
          ((targetSize h.rankThreshold xRank -
            min (restIt.length + 1) (targetSize h.rankThreshold xRank) : ℕ) : ℚ) + 1 := by
        exact_mod_cast hsub
      have hpop_step : popDeficit h.rankThreshold xPop ≤ popDeficit h.rankThreshold x + 12 := by
        dsimp only [popDeficit, xPop, x, SHTree.left, SHTree.right, SHTree.rank, SHTree.items]
        simp only [hnonleaf, ↓reduceIte, List.length_cons]
        linarith
      have hx_phi_s : xPop.phi h.rankThreshold ≤
          (SHTree.node xId xRank xCk (it₀ :: restIt) xLeft xRight).phi h.rankThreshold := hx_phi
      have hpop_s : popDeficit h.rankThreshold xPop ≤
          popDeficit h.rankThreshold (SHTree.node xId xRank xCk (it₀ :: restIt) xLeft xRight) +
            12 := hpop_step
      have hrc_eq : rootCredit xPop.rank =
          rootCredit (SHTree.node xId xRank xCk (it₀ :: restIt) xLeft xRight).rank := rfl
      simp only [totalPhi_append, totalPhi_cons, totalPhi_nil, add_zero]
      rw [hrc_eq]
      linarith

/-- Full specification of `shExtractMin`: extracts a minimum-key item (when non-empty),
maintains `SHInv` and pool framing, preserves item membership up to removal of the popped item,
never decreases any surviving entry's `ckey`, and spends `O(1)` amortized memory operations
(`+ 250`). -/
theorem shExtractMin_spec {w ic₀ nc₀ maxItems maxNodes fuel : ℕ}
    {h : SHHandle} {roots : List SHTree} {created : ℕ → ℕ} {s : Memory.State}
    (hinv : SHInv w ic₀ nc₀ maxItems maxNodes h roots created s)
    (hfuel_ge : shFuelBound h.rankThreshold maxItems ≤ fuel) (hf_fit : Fits w fuel) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (shExtractMin (h, fuel))) ∧
    shExtractMinSafe w (h, fuel) s ∧
    let res := (Memory.spec 0).clientResult s (shExtractMin (h, fuel))
    let h' := res.handle
    let found := res.found
    let val := res.val
    let popKey := res.key
    let s' := (Memory.spec 0).clientState s (shExtractMin (h, fuel))
    h'.itemBase = h.itemBase ∧
    h'.nodeBase = h.nodeBase ∧
    h'.itemCount = h.itemCount ∧
    h'.nodeCount = h.nodeCount ∧
    h'.rankThreshold = h.rankThreshold ∧
    s'.frontier = s.frontier ∧
    (∀ a, s'.mem a ≠ s.mem a → InSHPool ic₀ nc₀ maxItems maxNodes h a) ∧
    (roots = [] →
      found = 0 ∧ val = 0 ∧ popKey = 0 ∧ h' = h ∧ s' = s ∧
      memoryCost (shExtractMin (h, fuel)) s = 0) ∧
    (roots ≠ [] →
      found = 1 ∧
      ∃ it₀ roots',
        (it₀, popKey) ∈ forestEntries roots ∧
        it₀.val = val ∧
        it₀.origKey ≤ popKey ∧
        (∀ p ∈ forestEntries roots, popKey ≤ p.2) ∧
        SHInv w ic₀ nc₀ maxItems maxNodes h' roots' created s' ∧
        (it₀ :: forestItems roots').Perm (forestItems roots) ∧
        (∀ p ∈ forestEntries roots', ∃ c₀, (p.1, c₀) ∈ forestEntries roots ∧ c₀ ≤ p.2) ∧
        (memoryCost (shExtractMin (h, fuel)) s : ℚ) + totalPhi h.rankThreshold roots' ≤
          totalPhi h.rankThreshold roots + 250) := by
  have h16 := hinv.fits16
  have hwf := hinv.wf
  by_cases hne : roots = []
  · subst hne
    have hfr0 : h.firstRoot = 0 := by rw [hinv.firstRoot_eq]; rfl
    have hv_raw : (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s
          (shExtractMinRaw ![h.itemBase, h.nodeBase, h.firstRoot, fuel])) := by
      dsimp only [shExtractMinRaw]; simp +decide only [Matrix.cons_val, hfr0, ↓reduceIte]
      exact validHistory_pure w _ _
    have hsafe_raw : shExtractMinRawSafe w
        ![h.itemBase, h.nodeBase, h.firstRoot, fuel] s := by
      dsimp only [shExtractMinRawSafe]
      simp +decide only [Matrix.cons_val, hfr0]
      exact ⟨h16, False.elim⟩
    have hres_raw : (Memory.spec 0).clientResult s
        (shExtractMinRaw ![h.itemBase, h.nodeBase, h.firstRoot, fuel]) = (0, 0, 0, 0) := by
      dsimp only [shExtractMinRaw]; simp +decide only [Matrix.cons_val, hfr0, ↓reduceIte]; rfl
    have hs_raw : (Memory.spec 0).clientState s
        (shExtractMinRaw ![h.itemBase, h.nodeBase, h.firstRoot, fuel]) = s := by
      dsimp only [shExtractMinRaw]; simp +decide only [Matrix.cons_val, hfr0, ↓reduceIte]; rfl
    have hm_raw : memoryCost (shExtractMinRaw ![h.itemBase, h.nodeBase, h.firstRoot, fuel]) s =
        0 := by
      dsimp only [shExtractMinRaw]
      simp +decide only [Matrix.cons_val, hfr0, ↓reduceIte, memoryCost_pure]
    have hv_sh : (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (shExtractMin (h, fuel))) := by
      dsimp only [shExtractMin]
      exact validHistory_bind_step hv_raw (validHistory_pure w _ _)
    have hres_sh : (Memory.spec 0).clientResult s (shExtractMin (h, fuel)) =
        ⟨⟨h.itemBase, h.nodeBase, 0, h.itemCount, h.nodeCount, h.rankThreshold⟩, 0, 0, 0⟩ := by
      dsimp only [shExtractMin]; rw [StateTransitionSpec.clientResult_bind, hres_raw]; rfl
    have hs_sh : (Memory.spec 0).clientState s (shExtractMin (h, fuel)) = s := by
      dsimp only [shExtractMin]; rw [StateTransitionSpec.clientState_bind, hs_raw]; rfl
    have hm_sh : memoryCost (shExtractMin (h, fuel)) s = 0 := by
      dsimp only [shExtractMin]; rw [memoryCost_bind', hm_raw, memoryCost_pure]
    have hh_eq : (⟨h.itemBase, h.nodeBase, 0, h.itemCount, h.nodeCount,
        h.rankThreshold⟩ : SHHandle) = h := by
      cases h; simp only [SHHandle.mk.injEq, true_and, and_true]; exact hfr0.symm
    refine ⟨hv_sh, hsafe_raw, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun h0 => absurd rfl h0⟩
    · simp [hres_sh]
    · simp [hres_sh]
    · simp [hres_sh]
    · simp [hres_sh]
    · simp [hres_sh]
    · rw [hs_sh]
    · intro a ha; rw [hs_sh] at ha; exact absurd rfl ha
    · intro _
      simp only [hres_sh, hs_sh, hm_sh, hh_eq, and_self]
  · have hsm_spec := suffixMinTree_spec roots
    cases hsm : suffixMinTree roots with
    | none => rw [hsm] at hsm_spec; exact absurd hsm_spec hne
    | some x =>
      rw [hsm] at hsm_spec
      rcases hsm_spec with ⟨hx_in, hx_min⟩
      obtain ⟨pre, suf, hroots_eq⟩ := List.append_of_mem hx_in
      rw [← List.singleton_append, ← List.append_assoc] at hroots_eq
      have hx_val := hinv.trees_valid x hx_in
      have hfirst_pos : 0 < h.firstRoot := by
        rw [hinv.firstRoot_eq]
        cases hroots : roots with
        | nil => exact absurd hroots hne
        | cons r0 rs =>
          dsimp only [List.head?, Option.elim_some]
          have := (hinv.nodeIds_range r0.rootId
            (mem_forestNodeIds (by rw [hroots]; exact List.mem_cons_self)
              r0.rootId_mem_nodeIds)).1
          omega
      have hfirst_ne0 : h.firstRoot ≠ 0 := by omega
      have hfirst_lt : h.nodeBase + 12 * h.firstRoot + 11 < s.frontier := by
        rw [hinv.firstRoot_eq]
        cases hroots : roots with
        | nil => exact absurd hroots hne
        | cons r0 rs =>
          dsimp only [List.head?, Option.elim_some]
          have := (hinv.nodeIds_range r0.rootId
            (mem_forestNodeIds (by rw [hroots]; exact List.mem_cons_self)
              r0.rootId_mem_nodeIds)).2
          have := hinv.nc_max; have := hinv.node_pool_lt; omega
      have hsm_mem : s.mem (h.nodeBase + 12 * h.firstRoot + 11) = x.rootId := by
        have hsm_rl := hinv.rootList.suffixMin_eq hne
        rw [← hinv.firstRoot_eq, hsm] at hsm_rl
        exact hsm_rl
      have hmin_entries : ∀ p ∈ forestEntries roots, x.ckey ≤ p.2 := by
        intro p hp
        simp only [forestEntries, List.mem_flatMap] at hp
        rcases hp with ⟨t, ht, hp_t⟩
        exact Nat.le_trans (hx_min t ht) ((hinv.trees_valid t ht).ckey_le_allEntries p hp_t)
      rcases hx_items : x with ⟨xId, xRank, xCk, xItems, xLeft, xRight⟩
      rw [hx_items] at hx_val hx_in hroots_eq hsm_mem hmin_entries
      cases xItems with
      | nil => exact absurd rfl hx_val.items_ne
      | cons it₀ restIt =>
        let xNode : SHTree := .node xId xRank xCk (it₀ :: restIt) xLeft xRight
        let xPop : SHTree := .node xId xRank xCk restIt xLeft xRight
        have hinv_rw : SHInv w ic₀ nc₀ maxItems maxNodes h
            (pre ++ [xNode] ++ suf) created s := by
          simpa [xNode, ← hroots_eq] using hinv
        have hxNode_in : xNode ∈ pre ++ [xNode] ++ suf :=
          List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton.mpr rfl))
        have hxNode_mem := hinv_rw.trees_mem xNode hxNode_in
        have hxNode_lt : h.nodeBase + 12 * xId + 11 < s.frontier := by
          have := (hinv_rw.nodeIds_range xId
            (mem_forestNodeIds hxNode_in xNode.rootId_mem_nodeIds)).2
          have := hinv_rw.nc_max; have := hinv_rw.node_pool_lt; omega
        have hit0_lt : h.itemBase + 3 * it₀.id + 2 < s.frontier := by
          have hit_in : it₀.id ∈ xNode.itemIds := by
            simp only [xNode, SHTree.itemIds_node, List.mem_append]
            exact Or.inl (Or.inl (List.mem_map_of_mem (f := SHItem.id) List.mem_cons_self))
          have := (hinv_rw.itemIds_range it₀.id (itemIds_sub_mid pre xNode suf |>.mem hit_in)).2
          have := hinv_rw.ic_max; have := hinv_rw.item_pool_lt; omega
        have hsz_fit : Fits w restIt.length := by
          have hrest_le : restIt.length ≤ maxItems := by
            have hid_nd : xNode.itemIds.Nodup :=
              (itemIds_sub_mid pre xNode suf).nodup hinv_rw.itemIds_nodup
            have hit_nd : (xNode.itemIds.map (fun id => id - (ic₀ + 1))).Nodup := by
              refine List.Nodup.map_on ?_ hid_nd
              intro a ha b hb _
              have := (hinv_rw.itemIds_range a (itemIds_sub_mid pre xNode suf |>.mem ha)).1
              have := (hinv_rw.itemIds_range b (itemIds_sub_mid pre xNode suf |>.mem hb)).1
              omega
            have hx_len : xNode.itemIds.length ≤ maxItems := by
              rw [← List.length_map (f := fun id => id - (ic₀ + 1))]
              refine List.length_le_of_nodup_lt hit_nd ?_
              intro y hy
              rcases List.mem_map.mp hy with ⟨id, hid, rfl⟩
              have := hinv_rw.itemIds_range id (itemIds_sub_mid pre xNode suf |>.mem hid)
              have := hinv_rw.ic_max; omega
            simp only [xNode, SHTree.itemIds_node, List.length_append, List.length_map,
              List.length_cons] at hx_len
            omega
          have hsb : maxItems + 1 ≤ shFuelBound h.rankThreshold maxItems :=
            Nat.le_mul_of_pos_left _ (by omega)
          exact hinv_rw.fits_fuel.of_le (by omega)
        have hdisj_pop : ∀ it ∈ it₀ :: restIt, ∀ j < 12, ∀ k < 3,
            h.nodeBase + 12 * xId + j ≠ h.itemBase + 3 * it.id + k := by
          intro it hit j hj k hk
          have hid_le := (hinv_rw.nodeIds_range xId
            (mem_forestNodeIds hxNode_in xNode.rootId_mem_nodeIds)).2
          have hit_in : it.id ∈ xNode.itemIds := by
            simp only [xNode, SHTree.itemIds_node, List.mem_append]
            exact Or.inl (Or.inl (List.mem_map_of_mem (f := SHItem.id) hit))
          have hit_le := (hinv_rw.itemIds_range it.id
            (itemIds_sub_mid pre xNode suf |>.mem hit_in)).2
          have := hinv_rw.nc_max; have := hinv_rw.ic_max
          exact hinv_rw.pools_disj_node_item (nid := xId) (iid := it.id)
            (by omega) (by omega) hj hk
        have hpop := extractPopItem_spec h16 hwf hxNode_mem hxNode_lt hit0_lt hsz_fit hdisj_pop
        rcases hpop with ⟨hv_pop, hm_pop, hres_pop, hfr_pop, hmem_pop,
          h0_pop, h1_pop, h2_pop, h3_pop, hil_pop, hnil_pop⟩
        obtain ⟨s₁, hs₁_eq⟩ : ∃ s₁, s₁ = (Memory.spec 0).clientState s
            (extractPopItem ![h.itemBase, h.nodeBase, xId]) := ⟨_, rfl⟩
        rw [← hs₁_eq] at hfr_pop hmem_pop h0_pop h1_pop h2_pop h3_pop hil_pop hnil_pop
        have hwf₁ : Memory.WellFormed w s₁ := by
          rw [hs₁_eq]; exact wellFormed_clientState hwf hv_pop
        have hx_nd : xNode.nodeIds.Nodup :=
          (nodeIds_sub_mid pre xNode suf).nodup hinv_rw.nodeIds_nodup
        have hchild_mem : ∀ c, xLeft = some c ∨ xRight = some c →
            TreeMemRep h.rankThreshold h.itemBase h.nodeBase s₁.mem c := by
          intro c hc
          have hc_mem : TreeMemRep h.rankThreshold h.itemBase h.nodeBase s.mem c := by
            rcases hc with hl | hr
            · exact hxNode_mem.left_mem c hl
            · exact hxNode_mem.right_mem c hr
          refine TreeMemRep.congr (fun id hid j hj => ?_) (fun it hit k hk => ?_) hc_mem
          · symm; by_contra hdiff
            have hne : id ≠ xId := by
              intro heq
              have hnd_x := SHTree.nodeIds_head_not_mem
                (by dsimp only [xNode] at hx_nd; exact hx_nd)
              apply hnd_x
              rw [← heq]
              rcases hc with hl | hr
              · simp [hl, hid]
              · simp [hr, hid]
            rcases hmem_pop _ hdiff with h3 | h4 | h5 <;> omega
          · symm; by_contra hdiff
            have hit_in : it.id ∈ xNode.itemIds := by
              have hmem_ai : it ∈ xNode.allItems := by
                rcases hc with hl | hr
                · have hsub : c.allItems.Sublist xNode.allItems := by
                    simp only [xNode, SHTree.allItems, SHTree.allEntries_node, hl,
                      Option.elim_some, List.map_append]
                    exact List.Sublist.trans (List.sublist_append_right _ _)
                      (List.sublist_append_left _ _)
                  exact hsub.mem hit
                · have hsub : c.allItems.Sublist xNode.allItems := by
                    simp only [xNode, SHTree.allItems, SHTree.allEntries_node, hr,
                      Option.elim_some, List.map_append]
                    exact List.sublist_append_right _ _
                  exact hsub.mem hit
              exact List.mem_map_of_mem hmem_ai
            have hit_le := (hinv_rw.itemIds_range it.id
              (itemIds_sub_mid pre xNode suf |>.mem hit_in)).2
            have hid_le := (hinv_rw.nodeIds_range xId
              (mem_forestNodeIds hxNode_in xNode.rootId_mem_nodeIds)).2
            have := hinv_rw.nc_max; have := hinv_rw.ic_max
            rcases hmem_pop _ hdiff with h3 | h4 | h5
            · exact hinv_rw.pools_disj_node_item (nid := xId) (iid := it.id) (j := 3)
                (by omega) (by omega) (by decide) hk h3.symm
            · exact hinv_rw.pools_disj_node_item (nid := xId) (iid := it.id) (j := 4)
                (by omega) (by omega) (by decide) hk h4.symm
            · exact hinv_rw.pools_disj_node_item (nid := xId) (iid := it.id) (j := 5)
                (by omega) (by omega) (by decide) hk h5.symm
        have h6_pop : s₁.mem (h.nodeBase + 12 * xId + 6) = xLeft.elim 0 SHTree.rootId := by
          have : s₁.mem (h.nodeBase + 12 * xId + 6) = s.mem (h.nodeBase + 12 * xId + 6) := by
            by_contra hdiff; rcases hmem_pop _ hdiff with h3 | h4 | h5 <;> omega
          rw [this]; exact hxNode_mem.left_eq
        have h7_pop : s₁.mem (h.nodeBase + 12 * xId + 7) = xRight.elim 0 SHTree.rootId := by
          have : s₁.mem (h.nodeBase + 12 * xId + 7) = s.mem (h.nodeBase + 12 * xId + 7) := by
            by_contra hdiff; rcases hmem_pop _ hdiff with h3 | h4 | h5 <;> omega
          rw [this]; exact hxNode_mem.right_eq
        have hxPop_mem : TreeMemRep h.rankThreshold h.itemBase h.nodeBase s₁.mem xPop :=
          TreeMemRep.node hxNode_mem.rootId_ne h0_pop h1_pop h2_pop h3_pop hil_pop h6_pop h7_pop
            (fun c hc => hchild_mem c (Or.inl hc)) (fun c hc => hchild_mem c (Or.inr hc))
        have hfix := extractFixup_spec hinv_rw hfr_pop hwf₁ hmem_pop hxPop_mem hnil_pop
          hfuel_ge hf_fit
        rcases hfix with ⟨hv_fix, hsafe_fix, hfr_fix, hmem_fix, roots', hinv',
          hperm', hemono', hphi_fix⟩
        obtain ⟨s₂, hs₂_eq⟩ : ∃ s₂, s₂ = (Memory.spec 0).clientState s₁
            (extractFixup ![h.itemBase, h.nodeBase, h.firstRoot, xId, fuel]) := ⟨_, rfl⟩
        rw [← hs₂_eq] at hfr_fix hmem_fix hinv'
        have hsz_pre : 1 ≤ s.mem (h.nodeBase + 12 * xId + 3) := by
          have hsz_pre_eq : s.mem (h.nodeBase + 12 * xId + 3) = (it₀ :: restIt).length :=
            hxNode_mem.size_eq
          rw [hsz_pre_eq]
          simp only [List.length_cons]
          omega
        have hsm_rt : xId = s.mem (h.nodeBase + 12 * h.firstRoot + 11) := by
          simpa [SHTree.rootId] using hsm_mem.symm
        have hv_raw : (Memory.spec w).ValidHistory s
            ((Memory.spec w).clientHistory s
              (shExtractMinRaw ![h.itemBase, h.nodeBase, h.firstRoot, fuel])) := by
          dsimp only [shExtractMinRaw]
          simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
          simp only [hfirst_ne0, ↓reduceIte]
          refine validHistory_read_bind (by omega) ?_
          rw [← hsm_rt]
          refine validHistory_bind_step hv_pop ?_
          rw [← hs₁_eq]
          refine validHistory_bind_step hv_fix ?_
          exact validHistory_pure w _ _
        have hsafe_raw : shExtractMinRawSafe w
            ![h.itemBase, h.nodeBase, h.firstRoot, fuel] s := by
          dsimp only [shExtractMinRawSafe]; simp +decide only [Matrix.cons_val_zero,
                                              Matrix.cons_val_one, Matrix.cons_val]
          refine ⟨h16, fun _ => ?_⟩
          rw [← hsm_rt, ← hs₁_eq]
          exact ⟨hsz_pre, hsafe_fix⟩
        have hres_raw : (Memory.spec 0).clientResult s
            (shExtractMinRaw ![h.itemBase, h.nodeBase, h.firstRoot, fuel]) =
            ((Memory.spec 0).clientResult s₁
              (extractFixup ![h.itemBase, h.nodeBase, h.firstRoot, xId, fuel]),
              1, it₀.val, xCk) := by
          dsimp only [shExtractMinRaw]
          simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
          simp only [hfirst_ne0, ↓reduceIte]
          rw [clientResult_bind_read, ← hsm_rt, StateTransitionSpec.clientResult_bind,
            ← hs₁_eq, hres_pop, StateTransitionSpec.clientResult_bind]
          rfl
        have hs_raw : (Memory.spec 0).clientState s
            (shExtractMinRaw ![h.itemBase, h.nodeBase, h.firstRoot, fuel]) = s₂ := by
          dsimp only [shExtractMinRaw]
          simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
          simp only [hfirst_ne0, ↓reduceIte]
          rw [clientState_bind_read, ← hsm_rt, StateTransitionSpec.clientState_bind, ← hs₁_eq,
            StateTransitionSpec.clientState_bind, ← hs₂_eq]
          rfl
        have hm_raw : memoryCost
            (shExtractMinRaw ![h.itemBase, h.nodeBase, h.firstRoot, fuel]) s =
            1 + memoryCost (extractPopItem ![h.itemBase, h.nodeBase, xId]) s +
              memoryCost (extractFixup ![h.itemBase, h.nodeBase, h.firstRoot, xId, fuel]) s₁ := by
          dsimp only [shExtractMinRaw]
          simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
          simp only [hfirst_ne0, ↓reduceIte]
          rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read, ← hsm_rt,
            memoryCost_bind', ← hs₁_eq, memoryCost_bind', memoryCost_pure, add_zero]
          omega
        have hv_sh : (Memory.spec w).ValidHistory s
            ((Memory.spec w).clientHistory s (shExtractMin (h, fuel))) := by
          dsimp only [shExtractMin]
          exact validHistory_bind_step hv_raw (validHistory_pure w _ _)
        have hres_sh : (Memory.spec 0).clientResult s (shExtractMin (h, fuel)) =
            ⟨⟨h.itemBase, h.nodeBase,
              (Memory.spec 0).clientResult s₁
                (extractFixup ![h.itemBase, h.nodeBase, h.firstRoot, xId, fuel]),
              h.itemCount, h.nodeCount, h.rankThreshold⟩, 1, it₀.val, xCk⟩ := by
          dsimp only [shExtractMin]
          rw [StateTransitionSpec.clientResult_bind, hres_raw]
          rfl
        have hs_sh : (Memory.spec 0).clientState s (shExtractMin (h, fuel)) = s₂ := by
          dsimp only [shExtractMin]
          rw [StateTransitionSpec.clientState_bind, hs_raw]
          rfl
        have hm_sh : memoryCost (shExtractMin (h, fuel)) s =
            1 + memoryCost (extractPopItem ![h.itemBase, h.nodeBase, xId]) s +
              memoryCost (extractFixup ![h.itemBase, h.nodeBase, h.firstRoot, xId, fuel]) s₁ := by
          dsimp only [shExtractMin]
          rw [memoryCost_bind', memoryCost_pure, add_zero, hm_raw]
        have hmem_raw : ∀ a, s₂.mem a ≠ s.mem a → InSHPool ic₀ nc₀ maxItems maxNodes h a := by
          intro a ha
          by_cases h21 : s₂.mem a = s₁.mem a
          · rw [h21] at ha
            have hid_rng := hinv_rw.nodeIds_range xId
              (mem_forestNodeIds hxNode_in xNode.rootId_mem_nodeIds)
            have := hinv_rw.nc_max
            rcases hmem_pop _ ha with rfl | rfl | rfl <;>
              (right; constructor <;> omega)
          · exact hmem_fix a h21
        have hperm_final : (it₀ :: forestItems roots').Perm (forestItems roots) := by
          rw [hroots_eq]
          refine (List.Perm.cons it₀ hperm').trans ?_
          simp only [forestItems, forestEntries, List.flatMap_append, List.flatMap_cons,
            List.flatMap_nil, List.map_append, SHTree.allEntries_node,
            List.map_cons, List.append_assoc, List.cons_append]
          exact List.perm_middle.symm
        have hit₀_mem : (it₀, xCk) ∈ forestEntries roots := by
          rw [hroots_eq]
          simp only [forestEntries, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
            List.append_nil, List.mem_append, SHTree.allEntries_node, List.map_cons, List.mem_cons]
          exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl trivial))))
        refine ⟨hv_sh, hsafe_raw, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun h0 => absurd h0 hne, ?_⟩
        · simp [hres_sh]
        · simp [hres_sh]
        · simp [hres_sh]
        · simp [hres_sh]
        · simp [hres_sh]
        · rw [hs_sh]; exact hfr_fix.trans hfr_pop
        · intro a ha; rw [hs_sh] at ha; exact hmem_raw a ha
        · intro _
          refine ⟨by simp [hres_sh], it₀, roots', by simpa [hres_sh] using hit₀_mem,
            (by simp [hres_sh]), by simpa [hres_sh] using hinv.origKey_le_ckey (it₀, xCk) hit₀_mem,
            ?_, ?_, hperm_final, ?_, ?_⟩
          · simp only [hres_sh]; exact hmin_entries
          · simp only [hres_sh, hs_sh]; exact hinv'
          · intro pe hpe
            rcases hemono' pe hpe with ⟨c₀, hc₀, hle⟩
            refine ⟨c₀, ?_, hle⟩
            rw [hroots_eq]
            simp only [forestEntries, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
              List.append_nil, List.mem_append, SHTree.allEntries_node,
              List.map_cons, List.mem_cons] at hc₀ ⊢
            rcases hc₀ with (hp | hxpe) | hs
            · exact Or.inl (Or.inl hp)
            · exact Or.inl (Or.inr (by
                rcases hxpe with (hr1 | hr2) | hrr
                · exact Or.inl (Or.inl (Or.inr hr1))
                · exact Or.inl (Or.inr hr2)
                · exact Or.inr hrr))
            · exact Or.inr hs
          · rw [hm_sh]
            have hm_pop_q : (memoryCost (extractPopItem ![h.itemBase, h.nodeBase, xId]) s : ℚ) ≤
                8 := by exact_mod_cast hm_pop
            rw [hroots_eq]
            push_cast
            linarith

end Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap
