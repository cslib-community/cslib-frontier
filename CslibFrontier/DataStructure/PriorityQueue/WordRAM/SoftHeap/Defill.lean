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
-- `import all` reads `Program`'s `defillPickChild`, `defillSplice`, `defillFinish`, `defillStep`
-- (and `defill` body), plus `Model`'s `ItemListRep.*`, `TreeMemRep.*`, `SHTree.*` lemmas.
import all CslibFrontier.DataStructure.PriorityQueue.WordRAM.SoftHeap.Program
import all CslibFrontier.DataStructure.PriorityQueue.WordRAM.SoftHeap.Model
import CslibFrontier.Computability.WordRAM.Realization.ProgFrame
import CslibFrontier.DataStructure.Memory.Frame
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Zipper Invariant and Specification for Soft-Heap `defill`

Tracks the iterative `defill` cursor via a zipper (`ZipFrame`, `ZipCurValid`, `ZipInv`) and
proves `defill_spec`: restoring non-leaf item-list size `≥ targetSize rank` while maintaining
`SHTree.Valid`, tree framing, key monotonicity, and `memoryCost + t'.phi ≤ t₀.phi + 6`.

## Main definitions

* `Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap.ZipCurValid`: cursor validity invariant
  at entry to `defill`.

## Main results

* `Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap.defill_spec`: full functional correctness,
  framing, and potential-amortized memory-cost specification for `defill`.
-/

public section

namespace Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure Cslib.DataStructure.Memory

private structure ZipFrame where
  id : ℕ
  rank : ℕ
  ckey : ℕ
  items : List SHItem
  sibling : Option SHTree

private def zipPlug (f : ZipFrame) (c : SHTree) : SHTree :=
  .node f.id f.rank f.ckey f.items (some c) f.sibling

private def zipRebuild (cur : SHTree) : List ZipFrame → SHTree
  | [] => cur
  | f :: ctx => zipRebuild (zipPlug f cur) ctx

private theorem zipRebuild_nodeIds_sub (cur : SHTree) (ctx : List ZipFrame) :
    ∀ x ∈ cur.nodeIds, x ∈ (zipRebuild cur ctx).nodeIds := by
  induction ctx generalizing cur with
  | nil => intro x hx; exact hx
  | cons f ctx ih =>
    intro x hx
    apply ih
    simp [zipPlug, hx]

private theorem zipRebuild_rootId (cur : SHTree) (ctx : List ZipFrame) :
    (zipRebuild cur ctx).rootId = (ctx.getLast?.elim cur.rootId ZipFrame.id) := by
  induction ctx generalizing cur with
  | nil => rfl
  | cons f rest ih =>
    rw [zipRebuild, ih (zipPlug f cur)]
    cases rest <;> rfl

private theorem zipRebuild_rank (cur : SHTree) (ctx : List ZipFrame) :
    (ctx = [] → (zipRebuild cur ctx).rank = cur.rank) ∧
    (∀ f rest, ctx = f :: rest → (zipRebuild cur ctx).rank =
      (rest.getLast?.elim f.rank ZipFrame.rank)) := by
  induction ctx generalizing cur with
  | nil => simp [zipRebuild]
  | cons f rest ih =>
    constructor
    · intro h; cases h
    · intro f' rest' h
      cases h
      rw [zipRebuild]
      cases rest with
      | nil => simp [zipRebuild, zipPlug, SHTree.rank]
      | cons g rest2 =>
        have hih := (ih (zipPlug f cur)).2 g rest2 rfl
        cases rest2 with
        | nil => simpa [zipRebuild] using hih
        | cons h t =>
          simp only [List.getLast?_eq_some_getLast (List.cons_ne_nil h t)] at hih
          simp only [List.getLast?_eq_some_getLast (List.cons_ne_nil g (h :: t)),
            List.getLast_cons (List.cons_ne_nil h t)]
          exact hih

private theorem zipRebuild_countRank (k : ℕ) (cur : SHTree) (ctx : List ZipFrame) :
    (zipRebuild cur ctx).countRank k =
      cur.countRank k + (ctx.map (fun f =>
        (if f.rank = k then 1 else 0) + f.sibling.elim 0 (SHTree.countRank k))).sum := by
  induction ctx generalizing cur with
  | nil => simp [zipRebuild]
  | cons f rest ih =>
    rw [zipRebuild, ih (zipPlug f cur)]
    simp only [zipPlug, SHTree.countRank_node, List.map_cons, List.sum_cons, Option.elim_some]
    omega

private theorem zipRebuild_allEntries_perm (cur : SHTree) (ctx : List ZipFrame) :
    (zipRebuild cur ctx).allEntries.Perm (cur.allEntries ++
      ctx.flatMap (fun f => f.items.map (fun it => (it, f.ckey)) ++
        f.sibling.elim [] SHTree.allEntries)) := by
  induction ctx generalizing cur with
  | nil => simp [zipRebuild]
  | cons f rest ih =>
    rw [zipRebuild]
    refine (ih (zipPlug f cur)).trans ?_
    simp only [zipPlug, SHTree.allEntries_node, Option.elim_some, List.flatMap_cons]
    have hp : (f.items.map (fun it => (it, f.ckey)) ++ cur.allEntries ++
        f.sibling.elim [] SHTree.allEntries).Perm
        (cur.allEntries ++ (f.items.map (fun it => (it, f.ckey)) ++
          f.sibling.elim [] SHTree.allEntries)) := by
      rw [List.append_assoc]
      exact List.perm_append_comm_assoc _ _ _
    exact (List.Perm.append_right _ hp).trans (by simp [List.append_assoc])

private theorem zipRebuild_nodeIds_perm (cur : SHTree) (ctx : List ZipFrame) :
    (zipRebuild cur ctx).nodeIds.Perm (cur.nodeIds ++
      ctx.flatMap (fun f => f.id :: f.sibling.elim [] SHTree.nodeIds)) := by
  induction ctx generalizing cur with
  | nil => simp [zipRebuild]
  | cons f rest ih =>
    rw [zipRebuild]
    refine (ih (zipPlug f cur)).trans ?_
    simp only [zipPlug, SHTree.nodeIds_node, Option.elim_some, List.flatMap_cons]
    have hp : (f.id :: cur.nodeIds ++ f.sibling.elim [] SHTree.nodeIds).Perm
        (cur.nodeIds ++ (f.id :: f.sibling.elim [] SHTree.nodeIds)) := by
      have hp1 : ([f.id] ++ cur.nodeIds).Perm (cur.nodeIds ++ [f.id]) := List.perm_append_comm
      exact (List.Perm.append_right _ hp1).trans (by simp [List.append_assoc])
    exact (List.Perm.append_right _ hp).trans (by simp [List.append_assoc])

private theorem zipRebuild_phi (rt : ℕ) (cur : SHTree) (ctx : List ZipFrame) :
    (zipRebuild cur ctx).phi rt = cur.phi rt + (ctx.map (fun f =>
      120 * ((f.items.length : ℚ) * itemPhi rt f.rank +
        f.sibling.elim 0 (SHTree.itemPhiSum rt)) +
      30 * ((1 + f.sibling.elim 0 SHTree.nodeCount : ℕ) : ℚ))).sum := by
  induction ctx generalizing cur with
  | nil => simp [zipRebuild]
  | cons f rest ih =>
    rw [zipRebuild, ih (zipPlug f cur)]
    simp only [zipPlug, SHTree.phi, SHTree.itemPhiSum_node, SHTree.nodeCount_node,
      Option.elim_some, List.map_cons, List.sum_cons]
    push_cast
    ring

private def zipFrameRep (rt itemBase nodeBase : ℕ) (mem : ℕ → ℕ) (child : SHTree)
    (f : ZipFrame) : Prop :=
  f.id ≠ 0 ∧
  mem (nodeBase + 12 * f.id) = f.ckey ∧
  mem (nodeBase + 12 * f.id + 1) = f.rank ∧
  mem (nodeBase + 12 * f.id + 2) = targetSize rt f.rank ∧
  mem (nodeBase + 12 * f.id + 3) = f.items.length ∧
  ItemListRep itemBase mem (mem (nodeBase + 12 * f.id + 4))
    (mem (nodeBase + 12 * f.id + 5)) f.items ∧
  mem (nodeBase + 12 * f.id + 6) = child.rootId ∧
  mem (nodeBase + 12 * f.id + 7) = f.sibling.elim 0 SHTree.rootId ∧
  (∀ c, f.sibling = some c → TreeMemRep rt itemBase nodeBase mem c)

private def ZipFramesRep (rt itemBase nodeBase : ℕ) (mem : ℕ → ℕ) :
    SHTree → List ZipFrame → ℕ → Prop
  | child, [], lb => mem (nodeBase + 12 * child.rootId + 8) = 0 ∧ lb = 0
  | child, f :: rest, lb =>
      mem (nodeBase + 12 * child.rootId + 8) = f.id ∧
      f.items ≠ [] ∧
      f.items.length ≤ sizeCap rt f.rank ∧
      (∀ it ∈ f.items, it.origKey ≤ f.ckey) ∧
      (f.rank ≤ rt → ∀ it ∈ f.items, it.origKey = f.ckey) ∧
      child.rank + 1 = f.rank ∧
      (∀ sib, f.sibling = some sib → sib.rank + 1 = f.rank ∧ sib.Valid rt f.ckey) ∧
      zipFrameRep rt itemBase nodeBase mem child f ∧
      lb = f.ckey ∧
      ∃ lb', lb' ≤ f.ckey ∧ ZipFramesRep rt itemBase nodeBase mem (zipPlug f child) rest lb'

/-- Validity invariant for the active cursor subtree inside `defill` (allowing `items.length`
of the cursor node itself to be temporarily below `targetSize rt` when non-leaf). -/
@[expose] def ZipCurValid (rt lb : ℕ) (t : SHTree) : Prop :=
  t.items.length ≤ sizeCap rt t.rank ∧
  lb ≤ t.ckey ∧
  (∀ it ∈ t.items, it.origKey ≤ t.ckey) ∧
  (t.rank ≤ rt → ∀ it ∈ t.items, it.origKey = t.ckey) ∧
  (t.items = [] → t.left.isSome ∨ t.right.isSome) ∧
  (∀ c, t.left = some c → c.rank + 1 = t.rank ∧ c.Valid rt t.ckey) ∧
  (∀ c, t.right = some c → c.rank + 1 = t.rank ∧ c.Valid rt t.ckey)

private theorem ZipCurValid.toValid {rt lb : ℕ} {t : SHTree} (hval : ZipCurValid rt lb t)
    (hne : t.items ≠ [])
    (hpop : t.left.isSome ∨ t.right.isSome → targetSize rt t.rank ≤ t.items.length) :
    t.Valid rt lb := by
  cases t with
  | node id r ck items l r' =>
    rcases hval with ⟨hcap, hlb, hle, hk8, _, hl, hr⟩
    refine .node hne hcap hlb hle hk8 ?_ (fun c hc => (hl c hc).1) (fun c hc => (hl c hc).2)
      (fun c hc => (hr c hc).1) (fun c hc => (hr c hc).2)
    intro hch
    have hle1 := hpop hch
    dsimp only [SHTree.rank, SHTree.items] at hle1
    omega

private def ZipInv (rt w itemBase nodeBase : ℕ) (t₀ : SHTree)
    (cur? : Option SHTree) (ctx : List ZipFrame) (s : Memory.State) : Prop :=
  Fits w 16 ∧
  Memory.WellFormed w s ∧
  (∀ id ∈ t₀.nodeIds, nodeBase + 12 * id + 11 < s.frontier) ∧
  (∀ it ∈ t₀.allItems, itemBase + 3 * it.id + 2 < s.frontier) ∧
  (∀ id ∈ t₀.nodeIds, ∀ it ∈ t₀.allItems, ∀ j < 12, ∀ k < 3,
    nodeBase + 12 * id + j ≠ itemBase + 3 * it.id + k) ∧
  (match cur? with
   | none =>
       ctx = [] ∧
       ∃ t',
         t'.rootId = t₀.rootId ∧
         t'.rank = t₀.rank ∧
         t'.Valid rt 0 ∧
         (t'.left.isSome ∨ t'.right.isSome → targetSize rt t'.rank ≤ t'.items.length) ∧
         (t₀.items ≠ [] → t₀.ckey ≤ t'.ckey) ∧
         t'.nodeIds.Nodup ∧
         (∀ id ∈ t'.nodeIds, id ∈ t₀.nodeIds) ∧
         (∀ id ∈ t₀.nodeIds, id ∉ t'.nodeIds → s.mem (nodeBase + 12 * id + 4) = 0) ∧
         (∀ k, t'.countRank k ≤ t₀.countRank k) ∧
         t'.allItems.Perm t₀.allItems ∧
         (∀ p ∈ t'.allEntries, ∃ c₀, (p.1, c₀) ∈ t₀.allEntries ∧ c₀ ≤ p.2) ∧
         TreeMemRep rt itemBase nodeBase s.mem t' ∧
         s.mem (nodeBase + 12 * t'.rootId + 8) = 0
   | some cur =>
       let whole := zipRebuild cur ctx
       whole.rootId = t₀.rootId ∧
       whole.rank = t₀.rank ∧
       whole.nodeIds.Nodup ∧
       (∀ id ∈ whole.nodeIds, id ∈ t₀.nodeIds) ∧
       (∀ id ∈ t₀.nodeIds, id ∉ whole.nodeIds → s.mem (nodeBase + 12 * id + 4) = 0) ∧
       whole.itemIds.Nodup ∧
       (∀ k, whole.countRank k ≤ t₀.countRank k) ∧
       whole.allItems.Perm t₀.allItems ∧
       (∀ p ∈ whole.allEntries, ∃ c₀, (p.1, c₀) ∈ t₀.allEntries ∧ c₀ ≤ p.2) ∧
       (t₀.items ≠ [] → t₀.ckey ≤ whole.ckey) ∧
       TreeMemRep rt itemBase nodeBase s.mem cur ∧
       ∃ lb, ZipCurValid rt lb cur ∧ ZipFramesRep rt itemBase nodeBase s.mem cur ctx lb)

private def zipPhi (rt : ℕ) : Option SHTree → List ZipFrame → ℚ
  | none, _ => 0
  | some cur, ctx => (zipRebuild cur ctx).phi rt + 5 * (ctx.length : ℚ) + 5

private theorem zipPhi_nonneg (rt : ℕ) (cur? : Option SHTree) (ctx : List ZipFrame) :
    0 ≤ zipPhi rt cur? ctx := by
  cases cur? with
  | none => exact le_rfl
  | some cur =>
    unfold zipPhi
    have h1 := (zipRebuild cur ctx).phi_nonneg rt
    have h2 : (0 : ℚ) ≤ (ctx.length : ℚ) := Nat.cast_nonneg _
    linarith


private theorem defillPickChild_spec {rt w itemBase nodeBase : ℕ} {s : Memory.State} {t : SHTree}
    {l₀ r₀ : ℕ}
    (h16 : Fits w 16) (hmem : Memory.WellFormed w s)
    (ht_mem : TreeMemRep rt itemBase nodeBase s.mem t)
    (hnonleaf : t.left.isSome ∨ t.right.isSome)
    (hn_lt : ∀ id ∈ t.nodeIds, nodeBase + 12 * id + 11 < s.frontier)
    (hl0 : l₀ = t.left.elim 0 SHTree.rootId)
    (hr0 : r₀ = t.right.elim 0 SHTree.rootId) :
    let d : Fin 4 → ℕ := ![nodeBase, t.rootId, l₀, r₀]
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (defillPickChild d)) ∧
    let cIdx := (Memory.spec 0).clientResult s (defillPickChild d)
    let s' := (Memory.spec 0).clientState s (defillPickChild d)
    memoryCost (defillPickChild d) s ≤ 4 ∧
    s'.frontier = s.frontier ∧
    (∀ a, a ≠ nodeBase + 12 * t.rootId + 6 → a ≠ nodeBase + 12 * t.rootId + 7 →
      s'.mem a = s.mem a) ∧
    ∃ c sib,
      ((t.left = some c ∧ t.right = sib) ∨ (t.right = some c ∧ t.left = sib)) ∧
      cIdx = c.rootId ∧
      s'.mem (nodeBase + 12 * t.rootId + 6) = c.rootId ∧
      s'.mem (nodeBase + 12 * t.rootId + 7) = sib.elim 0 SHTree.rootId ∧
      (∀ sc, sib = some sc → c.ckey ≤ sc.ckey) := by
  have hcr_pure : ∀ (x : ℕ) (t' : Memory.State),
      (Memory.spec 0).clientResult t' (Pure.pure x) = x := fun _ _ => rfl
  have hcs_pure : ∀ (x : ℕ) (t' : Memory.State),
      (Memory.spec 0).clientState t' (Pure.pure x) = t' := fun _ _ => rfl
  have hmc_pure : ∀ (x : ℕ) (t' : Memory.State),
      memoryCost (Pure.pure x) t' = 0 := fun _ _ => rfl
  cases t with
  | node id rank ck items l r' =>
    rcases ht_mem with ⟨hid, _, _, _, _, _, h6, h7, hl, hr⟩
    subst hl0; subst hr0
    dsimp only [SHTree.rootId, SHTree.left, SHTree.right] at *
    have hid_lt : nodeBase + 12 * id + 11 < s.frontier := hn_lt id (by simp)
    cases l with
    | none =>
      cases r' with
      | none => simp at hnonleaf
      | some cr =>
        have hcr_mem := hr cr rfl
        have hcr_fit : Fits w cr.rootId := hmem.fits_of_lt_frontier
          (by have := hn_lt cr.rootId (by simp [SHTree.rootId_mem_nodeIds]); omega)
        have h0_fit : Fits w 0 := h16.of_le (by omega)
        dsimp only [defillPickChild]
        simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
          Option.elim_none, Option.elim_some, ↓reduceIte]
        have hs_eq : (Memory.spec 0).clientState s
            (do
              Memory.write (nodeBase + 12 * id + 6) cr.rootId
              Memory.write (nodeBase + 12 * id + 7) 0
              pure cr.rootId) =
            ⟨Function.update (Function.update s.mem (nodeBase + 12 * id + 6) cr.rootId)
              (nodeBase + 12 * id + 7) 0, s.frontier⟩ := rfl
        refine ⟨validHistory_write_bind (by omega) hcr_fit
          (validHistory_write_bind (by dsimp only; omega) h0_fit (validHistory_pure w _ _)),
          ?_, ?_, ?_, cr, none, Or.inr ⟨rfl, rfl⟩, ?_, ?_, ?_, fun _ h => by cases h⟩
        · simp only [memoryCost_bind', memoryCost_write, hmc_pure]; decide
        · rw [hs_eq]
        · intro a ha6 ha7
          rw [hs_eq]; dsimp only
          rw [Function.update_of_ne ha7, Function.update_of_ne ha6]
        · rfl
        · rw [hs_eq]; dsimp only
          rw [Function.update_of_ne (by omega), Function.update_self]; rfl
        · rw [hs_eq]; dsimp only
          rw [Function.update_self]; rfl
    | some cl =>
      have hcl_mem := hl cl rfl
      have hcl_ne : cl.rootId ≠ 0 := hcl_mem.rootId_ne
      have hcl_lt : nodeBase + 12 * cl.rootId + 11 < s.frontier :=
        hn_lt cl.rootId (by simp [SHTree.rootId_mem_nodeIds])
      cases r' with
      | none =>
        dsimp only [defillPickChild]
        simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
          Option.elim_some, Option.elim_none, hcl_ne, ↓reduceIte]
        exact ⟨validHistory_read (by omega), by rw [memoryCost_read]; decide, rfl,
          fun _ _ _ => rfl, cl, none, Or.inl ⟨rfl, rfl⟩, h6, h6, h7,
          fun _ h => by cases h⟩
      | some cr =>
        have hcr_mem := hr cr rfl
        have hcr_ne : cr.rootId ≠ 0 := hcr_mem.rootId_ne
        have hcr_lt : nodeBase + 12 * cr.rootId + 11 < s.frontier :=
          hn_lt cr.rootId (by simp [SHTree.rootId_mem_nodeIds])
        have hcl_ck : s.mem (nodeBase + 12 * cl.rootId) = cl.ckey := hcl_mem.ckey_eq
        have hcr_ck : s.mem (nodeBase + 12 * cr.rootId) = cr.ckey := hcr_mem.ckey_eq
        have hcl_fit : Fits w cl.rootId := hmem.fits_of_lt_frontier (by omega)
        have hcr_fit : Fits w cr.rootId := hmem.fits_of_lt_frontier (by omega)
        dsimp only [defillPickChild]
        simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
          Option.elim_some, hcl_ne, hcr_ne, ↓reduceIte]
        by_cases hcmp : cr.ckey < cl.ckey
        · have hs_eq : (Memory.spec 0).clientState s
              (do
                let lc ← Memory.read (nodeBase + 12 * cl.rootId)
                let rc ← Memory.read (nodeBase + 12 * cr.rootId)
                if rc < lc then do
                  Memory.write (nodeBase + 12 * id + 6) cr.rootId
                  Memory.write (nodeBase + 12 * id + 7) cl.rootId
                  pure cr.rootId
                else pure cl.rootId) =
              ⟨Function.update (Function.update s.mem (nodeBase + 12 * id + 6) cr.rootId)
                (nodeBase + 12 * id + 7) cl.rootId, s.frontier⟩ := by
            repeat rw [clientState_bind_read]
            rw [hcl_ck, hcr_ck]
            simp only [hcmp, ↓reduceIte]
            rfl
          have hres_eq : (Memory.spec 0).clientResult s
              (do
                let lc ← Memory.read (nodeBase + 12 * cl.rootId)
                let rc ← Memory.read (nodeBase + 12 * cr.rootId)
                if rc < lc then do
                  Memory.write (nodeBase + 12 * id + 6) cr.rootId
                  Memory.write (nodeBase + 12 * id + 7) cl.rootId
                  pure cr.rootId
                else pure cl.rootId) = cr.rootId := by
            repeat rw [clientResult_bind_read]
            rw [hcl_ck, hcr_ck]
            simp only [hcmp, ↓reduceIte]
            rfl
          refine ⟨validHistory_read_bind (by omega) (validHistory_read_bind (by omega) ?_),
            ?_, ?_, ?_, cr, some cl, Or.inr ⟨rfl, rfl⟩, ?_, ?_, ?_,
            fun sc hsc => by cases hsc; omega⟩
          · rw [hcl_ck, hcr_ck]; simp only [hcmp, ↓reduceIte]
            exact validHistory_write_bind (by omega) hcr_fit
              (validHistory_write_bind (by dsimp only; omega) hcl_fit (validHistory_pure w _ _))
          · repeat (rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read])
            rw [hcl_ck, hcr_ck]
            simp only [hcmp, ↓reduceIte, memoryCost_bind', memoryCost_write, hmc_pure]
            decide
          · rw [hs_eq]
          · intro a ha6 ha7
            rw [hs_eq]; dsimp only
            rw [Function.update_of_ne ha7, Function.update_of_ne ha6]
          · exact hres_eq
          · rw [hs_eq]; dsimp only
            rw [Function.update_of_ne (by omega), Function.update_self]; rfl
          · rw [hs_eq]; dsimp only
            rw [Function.update_self]; rfl
        · have hs_eq : (Memory.spec 0).clientState s
              (do
                let lc ← Memory.read (nodeBase + 12 * cl.rootId)
                let rc ← Memory.read (nodeBase + 12 * cr.rootId)
                if rc < lc then do
                  Memory.write (nodeBase + 12 * id + 6) cr.rootId
                  Memory.write (nodeBase + 12 * id + 7) cl.rootId
                  pure cr.rootId
                else pure cl.rootId) = s := by
            repeat rw [clientState_bind_read]
            rw [hcl_ck, hcr_ck]
            simp only [hcmp, ↓reduceIte]
            rfl
          have hres_eq : (Memory.spec 0).clientResult s
              (do
                let lc ← Memory.read (nodeBase + 12 * cl.rootId)
                let rc ← Memory.read (nodeBase + 12 * cr.rootId)
                if rc < lc then do
                  Memory.write (nodeBase + 12 * id + 6) cr.rootId
                  Memory.write (nodeBase + 12 * id + 7) cl.rootId
                  pure cr.rootId
                else pure cl.rootId) = cl.rootId := by
            repeat rw [clientResult_bind_read]
            rw [hcl_ck, hcr_ck]
            simp only [hcmp, ↓reduceIte]
            rfl
          refine ⟨validHistory_read_bind (by omega) (validHistory_read_bind (by omega) ?_),
            ?_, ?_, ?_, cl, some cr, Or.inl ⟨rfl, rfl⟩, ?_, ?_, ?_,
            fun sc hsc => by cases hsc; omega⟩
          · rw [hcl_ck, hcr_ck]; simp only [hcmp, ↓reduceIte]; exact validHistory_pure w _ _
          · repeat (rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read])
            rw [hcl_ck, hcr_ck]
            simp only [hcmp, ↓reduceIte, hmc_pure]
            decide
          · rw [hs_eq]
          · intro _ _ _; rw [hs_eq]
          · exact hres_eq
          · rw [hs_eq]; exact h6
          · rw [hs_eq]; exact h7

private theorem defillSplice_spec {rt w itemBase nodeBase : ℕ} {s : Memory.State}
    {cur c : SHTree}
    (h16 : Fits w 16) (hmem : Memory.WellFormed w s)
    (hcur_mem : TreeMemRep rt itemBase nodeBase s.mem cur)
    (hc_mem : TreeMemRep rt itemBase nodeBase s.mem c)
    (hc_ne : c.items ≠ [])
    (hcur_c : cur.rootId ≠ c.rootId)
    (hitem_nodup : (cur.items.map SHItem.id).Nodup)
    (hitem_disj : ∀ x ∈ cur.items, ∀ y ∈ c.items, x.id ≠ y.id)
    (hn_cur : nodeBase + 12 * cur.rootId + 11 < s.frontier)
    (hn_c : nodeBase + 12 * c.rootId + 11 < s.frontier)
    (hi_cur : ∀ it ∈ cur.items, itemBase + 3 * it.id + 2 < s.frontier)
    (hi_c : ∀ it ∈ c.items, itemBase + 3 * it.id + 2 < s.frontier)
    (hc_nodup : (c.items.map SHItem.id).Nodup)
    (hdisj : ∀ id, id = cur.rootId ∨ id = c.rootId →
      ∀ it ∈ cur.items ++ c.items, ∀ j < 12, ∀ k < 3,
        nodeBase + 12 * id + j ≠ itemBase + 3 * it.id + k) :
    let d : Fin 5 → ℕ := ![itemBase, nodeBase, cur.rootId, c.rootId, cur.items.length]
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (defillSplice d)) ∧
    let s' := (Memory.spec 0).clientState s (defillSplice d)
    memoryCost (defillSplice d) s ≤ 13 ∧
    s'.frontier = s.frontier ∧
    (∀ a, a ≠ nodeBase + 12 * cur.rootId → a ≠ nodeBase + 12 * cur.rootId + 3 →
      a ≠ nodeBase + 12 * cur.rootId + 4 → a ≠ nodeBase + 12 * cur.rootId + 5 →
      a ≠ nodeBase + 12 * c.rootId + 3 → a ≠ nodeBase + 12 * c.rootId + 4 →
      a ≠ nodeBase + 12 * c.rootId + 5 →
      (cur.items = [] ∨ a ≠ itemBase + 3 * s.mem (nodeBase + 12 * cur.rootId + 5) + 2) →
      s'.mem a = s.mem a) ∧
    s'.mem (nodeBase + 12 * cur.rootId) = c.ckey ∧
    s'.mem (nodeBase + 12 * cur.rootId + 3) = (cur.items ++ c.items).length ∧
    ItemListRep itemBase s'.mem (s'.mem (nodeBase + 12 * cur.rootId + 4))
      (s'.mem (nodeBase + 12 * cur.rootId + 5)) (cur.items ++ c.items) ∧
    s'.mem (nodeBase + 12 * c.rootId + 3) = 0 ∧
    s'.mem (nodeBase + 12 * c.rootId + 4) = 0 ∧
    s'.mem (nodeBase + 12 * c.rootId + 5) = 0 := by
  cases cur with
  | node id₁ r₁ ck₁ items₁ l₁ r₁' =>
    cases c with
    | node id₂ r₂ ck₂ items₂ l₂ r₂' =>
      rcases hcur_mem with ⟨hid₁, _, _, _, _, h45₁, _, _, _, _⟩
      rcases hc_mem with ⟨hid₂, hc0, _, _, hc3, h45₂, _, _, _, _⟩
      dsimp only [SHTree.rootId, SHTree.items, SHTree.ckey] at *
      have hfront : s.frontier < 2 ^ w := hmem.frontier_fits
      have h0_fit : Fits w 0 := h16.of_le (by omega)
      have hck2_fit : Fits w ck₂ := by rw [← hc0]; exact hmem.mem_fits _
      have hfit_cHead : Fits w (s.mem (nodeBase + 12 * id₂ + 4)) := hmem.mem_fits _
      have hfit_cTail : Fits w (s.mem (nodeBase + 12 * id₂ + 5)) := hmem.mem_fits _
      have hlen_fit : Fits w (items₁ ++ items₂).length := by
        have hnd12 : ((items₁ ++ items₂).map SHItem.id).Nodup := by
          rw [List.map_append, List.nodup_append]
          refine ⟨hitem_nodup, hc_nodup, fun x hx y hy => ?_⟩
          simp only [List.mem_map] at hx hy
          rcases hx with ⟨a, ha, rfl⟩
          rcases hy with ⟨b, hb, rfl⟩
          exact hitem_disj a ha b hb
        have hle_b : ∀ y ∈ (items₁ ++ items₂).map SHItem.id, y < s.frontier := by
          intro y hy
          simp only [List.mem_map, List.mem_append] at hy
          rcases hy with ⟨it, hit | hit, rfl⟩
          · have := hi_cur it hit; omega
          · have := hi_c it hit; omega
        simpa using subperm_length_fits (ys := (items₁ ++ items₂).map SHItem.id)
          (fun _ h => h) hnd12 hle_b hfront
      have hfit_sum : Fits w (items₁.length + items₂.length) := by simpa using hlen_fit
      have h_app := ItemListRep.append hc_ne hitem_nodup hitem_disj h45₁ h45₂
      by_cases h1 : items₁ = []
      · subst h1
        rcases h45₁ with ⟨hcur4, _⟩
        have hhv_nil : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
            (defillSplice ![itemBase, nodeBase, id₁, id₂, ([] : List SHItem).length])) := by
          dsimp only [defillSplice]
          simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
          refine validHistory_read_bind (by omega) (validHistory_read_bind (by omega)
            (validHistory_read_bind (by omega) (validHistory_read_bind (by omega)
              (validHistory_read_bind (by omega) ?_))))
          rw [hc0, hc3, hcur4]
          simp only [↓reduceIte]
          exact validHistory_write_bind (by omega) hfit_cHead
            (validHistory_write_bind (by dsimp only; omega) hfit_cTail
              (validHistory_write_bind (by dsimp only; omega) hfit_sum
                (validHistory_write_bind (by dsimp only; omega) hck2_fit
                  (validHistory_write_bind (by dsimp only; omega) h0_fit
                    (validHistory_write_bind (by dsimp only; omega) h0_fit
                      (validHistory_write (by dsimp only; omega) h0_fit))))))
        have hm_nil : memoryCost
            (defillSplice ![itemBase, nodeBase, id₁, id₂, ([] : List SHItem).length]) s ≤ 13 := by
          dsimp only [defillSplice]
          simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
          repeat (rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read])
          rw [hc0, hc3, hcur4]
          simp only [↓reduceIte, memoryCost_bind', memoryCost_write]
          decide
        have hs_nil : (Memory.spec 0).clientState s
            (defillSplice ![itemBase, nodeBase, id₁, id₂, ([] : List SHItem).length]) =
            let m₁ := Function.update s.mem (nodeBase + 12 * id₁ + 4)
              (s.mem (nodeBase + 12 * id₂ + 4))
            let m₂ := Function.update m₁ (nodeBase + 12 * id₁ + 5)
              (s.mem (nodeBase + 12 * id₂ + 5))
            let m₃ := Function.update m₂ (nodeBase + 12 * id₁ + 3)
              (([] : List SHItem).length + items₂.length)
            let m₄ := Function.update m₃ (nodeBase + 12 * id₁) ck₂
            let m₅ := Function.update m₄ (nodeBase + 12 * id₂ + 4) 0
            let m₆ := Function.update m₅ (nodeBase + 12 * id₂ + 5) 0
            ⟨Function.update m₆ (nodeBase + 12 * id₂ + 3) 0, s.frontier⟩ := by
          dsimp only [defillSplice]
          simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
          repeat rw [clientState_bind_read]
          rw [hc0, hc3, hcur4]
          simp only [↓reduceIte]
          rfl
        rw [hs_nil]
        refine ⟨hhv_nil, hm_nil, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro a ha0 ha3 ha4 ha5 hc3' hc4' hc5' _
          dsimp only
          rw [Function.update_of_ne hc3', Function.update_of_ne hc5',
            Function.update_of_ne hc4', Function.update_of_ne ha0,
            Function.update_of_ne ha3, Function.update_of_ne ha5, Function.update_of_ne ha4]
        · dsimp only
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_self]
        · dsimp only
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_self]; simp
        · dsimp only
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_self, Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_self]
          simp only [List.nil_append, hcur4, ↓reduceIte] at h_app ⊢
          refine ItemListRep.congr (fun it hit j hj => ?_) h_app
          have hit' : it ∈ [] ++ items₂ := List.mem_append_right _ hit
          have hd1 := hdisj id₁ (Or.inl rfl) it hit'
          have hd2 := hdisj id₂ (Or.inr rfl) it hit'
          have hne0 : itemBase + 3 * it.id + j ≠ nodeBase + 12 * id₁ := by
            simpa using (hd1 0 (by decide) j hj).symm
          rw [Function.update_of_ne (hd2 3 (by decide) j hj).symm,
            Function.update_of_ne (hd2 5 (by decide) j hj).symm,
            Function.update_of_ne (hd2 4 (by decide) j hj).symm,
            Function.update_of_ne hne0,
            Function.update_of_ne (hd1 3 (by decide) j hj).symm,
            Function.update_of_ne (hd1 5 (by decide) j hj).symm,
            Function.update_of_ne (hd1 4 (by decide) j hj).symm]
        · dsimp only
          rw [Function.update_self]
        · dsimp only
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_self]
        · dsimp only
          rw [Function.update_of_ne (by omega), Function.update_self]
      · have hcur4_ne : s.mem (nodeBase + 12 * id₁ + 4) ≠ 0 := by
          intro hz; exact h1 ((ItemListRep.head_eq_zero_iff h45₁).mp hz)
        rcases ItemListRep.tail_mem h1 h45₁ with ⟨it_last, hit_last, htail_eq, _⟩
        have htail_lt : itemBase + 3 * s.mem (nodeBase + 12 * id₁ + 5) + 2 < s.frontier := by
          rw [htail_eq]; exact hi_cur it_last hit_last
        have hlast_mem : it_last ∈ items₁ ++ items₂ := List.mem_append_left _ hit_last
        have hd1_last := hdisj id₁ (Or.inl rfl) it_last hlast_mem
        have hd2_last := hdisj id₂ (Or.inr rfl) it_last hlast_mem
        have hc4_disj : itemBase + 3 * s.mem (nodeBase + 12 * id₁ + 5) + 2 ≠
            nodeBase + 12 * id₁ + 4 := by
          rw [htail_eq]; exact (hd1_last 4 (by decide) 2 (by decide)).symm
        have hc5_disj : itemBase + 3 * s.mem (nodeBase + 12 * id₁ + 5) + 2 ≠
            nodeBase + 12 * id₁ + 5 := by
          rw [htail_eq]; exact (hd1_last 5 (by decide) 2 (by decide)).symm
        have hc3_disj : itemBase + 3 * s.mem (nodeBase + 12 * id₁ + 5) + 2 ≠
            nodeBase + 12 * id₁ + 3 := by
          rw [htail_eq]; exact (hd1_last 3 (by decide) 2 (by decide)).symm
        have hc0_disj : itemBase + 3 * s.mem (nodeBase + 12 * id₁ + 5) + 2 ≠
            nodeBase + 12 * id₁ := by
          rw [htail_eq]; exact (hd1_last 0 (by decide) 2 (by decide)).symm
        have hc4_c_disj : itemBase + 3 * s.mem (nodeBase + 12 * id₁ + 5) + 2 ≠
            nodeBase + 12 * id₂ + 4 := by
          rw [htail_eq]; exact (hd2_last 4 (by decide) 2 (by decide)).symm
        have hc5_c_disj : itemBase + 3 * s.mem (nodeBase + 12 * id₁ + 5) + 2 ≠
            nodeBase + 12 * id₂ + 5 := by
          rw [htail_eq]; exact (hd2_last 5 (by decide) 2 (by decide)).symm
        have hc3_c_disj : itemBase + 3 * s.mem (nodeBase + 12 * id₁ + 5) + 2 ≠
            nodeBase + 12 * id₂ + 3 := by
          rw [htail_eq]; exact (hd2_last 3 (by decide) 2 (by decide)).symm
        have hhv_cons : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
            (defillSplice ![itemBase, nodeBase, id₁, id₂, items₁.length])) := by
          dsimp only [defillSplice]
          simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
          refine validHistory_read_bind (by omega) (validHistory_read_bind (by omega)
            (validHistory_read_bind (by omega) (validHistory_read_bind (by omega)
              (validHistory_read_bind (by omega) ?_))))
          rw [hc0, hc3]
          simp only [hcur4_ne, ↓reduceIte]
          refine validHistory_read_bind (by omega) ?_
          exact validHistory_write_bind htail_lt hfit_cHead
            (validHistory_write_bind (by dsimp only; omega) hfit_cTail
              (validHistory_write_bind (by dsimp only; omega) hfit_sum
                (validHistory_write_bind (by dsimp only; omega) hck2_fit
                  (validHistory_write_bind (by dsimp only; omega) h0_fit
                    (validHistory_write_bind (by dsimp only; omega) h0_fit
                      (validHistory_write (by dsimp only; omega) h0_fit))))))
        have hm_cons : memoryCost
            (defillSplice ![itemBase, nodeBase, id₁, id₂, items₁.length]) s ≤ 13 := by
          dsimp only [defillSplice]
          simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
          repeat (rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read])
          rw [hc0, hc3]
          simp only [hcur4_ne, ↓reduceIte, memoryCost_bind', memoryCost_read, memoryCost_write]
          decide
        have hs_cons : (Memory.spec 0).clientState s
            (defillSplice ![itemBase, nodeBase, id₁, id₂, items₁.length]) =
            let m₁ := Function.update s.mem (itemBase + 3 * s.mem (nodeBase + 12 * id₁ + 5) + 2)
              (s.mem (nodeBase + 12 * id₂ + 4))
            let m₂ := Function.update m₁ (nodeBase + 12 * id₁ + 5)
              (s.mem (nodeBase + 12 * id₂ + 5))
            let m₃ := Function.update m₂ (nodeBase + 12 * id₁ + 3) (items₁.length + items₂.length)
            let m₄ := Function.update m₃ (nodeBase + 12 * id₁) ck₂
            let m₅ := Function.update m₄ (nodeBase + 12 * id₂ + 4) 0
            let m₆ := Function.update m₅ (nodeBase + 12 * id₂ + 5) 0
            ⟨Function.update m₆ (nodeBase + 12 * id₂ + 3) 0, s.frontier⟩ := by
          dsimp only [defillSplice]
          simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
          repeat rw [clientState_bind_read]
          rw [hc0, hc3]
          simp only [hcur4_ne, ↓reduceIte]
          rfl
        rw [hs_cons]
        refine ⟨hhv_cons, hm_cons, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro a ha0 ha3 ha4 ha5 hc3' hc4' hc5' hlast
          rcases hlast with hnil | hlast
          · exact absurd hnil h1
          · dsimp only
            rw [Function.update_of_ne hc3', Function.update_of_ne hc5',
              Function.update_of_ne hc4', Function.update_of_ne ha0,
              Function.update_of_ne ha3, Function.update_of_ne ha5,
              Function.update_of_ne hlast]
        · dsimp only
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_self]
        · dsimp only
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_self]; simp
        · dsimp only
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne hc4_disj.symm, Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_self]
          simp only [hcur4_ne, ↓reduceIte] at h_app ⊢
          refine ItemListRep.congr (fun it hit j hj => ?_) h_app
          have hd1 := hdisj id₁ (Or.inl rfl) it hit
          have hd2 := hdisj id₂ (Or.inr rfl) it hit
          have hne0 : itemBase + 3 * it.id + j ≠ nodeBase + 12 * id₁ := by
            simpa using (hd1 0 (by decide) j hj).symm
          rw [Function.update_of_ne (hd2 3 (by decide) j hj).symm,
            Function.update_of_ne (hd2 5 (by decide) j hj).symm,
            Function.update_of_ne (hd2 4 (by decide) j hj).symm,
            Function.update_of_ne hne0,
            Function.update_of_ne (hd1 3 (by decide) j hj).symm,
            Function.update_of_ne (hd1 5 (by decide) j hj).symm]
        · dsimp only
          rw [Function.update_self]
        · dsimp only
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_self]
        · dsimp only
          rw [Function.update_of_ne (by omega), Function.update_self]

private theorem defillFinish_spec {w nodeBase : ℕ} {s : Memory.State}
    {curId cId cLeft cRight nr : ℕ}
    (h16 : Fits w 16) (hmem : Memory.WellFormed w s)
    (_hcur_c : curId ≠ cId)
    (h6 : s.mem (nodeBase + 12 * cId + 6) = cLeft)
    (h7 : s.mem (nodeBase + 12 * cId + 7) = cRight)
    (hnr : s.mem (nodeBase + 12 * curId + 7) = nr)
    (hn_cur : nodeBase + 12 * curId + 11 < s.frontier)
    (hn_c : nodeBase + 12 * cId + 11 < s.frontier)
    (hcur_fit : Fits w curId) :
    let d : Fin 3 → ℕ := ![nodeBase, curId, cId]
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (defillFinish d)) ∧
    let nxt := (Memory.spec 0).clientResult s (defillFinish d)
    let s' := (Memory.spec 0).clientState s (defillFinish d)
    s'.frontier = s.frontier ∧
    if cLeft = 0 ∧ cRight = 0 then
      memoryCost (defillFinish d) s ≤ 5 ∧
      nxt = curId ∧
      s'.mem (nodeBase + 12 * curId + 6) = nr ∧
      s'.mem (nodeBase + 12 * curId + 7) = 0 ∧
      ∀ a, a ≠ nodeBase + 12 * curId + 6 → a ≠ nodeBase + 12 * curId + 7 → s'.mem a = s.mem a
    else
      memoryCost (defillFinish d) s ≤ 3 ∧
      nxt = cId ∧
      s'.mem (nodeBase + 12 * cId + 8) = curId ∧
      ∀ a, a ≠ nodeBase + 12 * cId + 8 → s'.mem a = s.mem a := by
  have h0_fit : Fits w 0 := h16.of_le (by omega)
  have hnr_fit : Fits w nr := by rw [← hnr]; exact hmem.mem_fits _
  have hcr_pure : ∀ (x : ℕ) (t : Memory.State),
      (Memory.spec 0).clientResult t (Pure.pure x) = x := fun _ _ => rfl
  have hcs_pure : ∀ (x : ℕ) (t : Memory.State),
      (Memory.spec 0).clientState t (Pure.pure x) = t := fun _ _ => rfl
  have hmc_pure : ∀ (x : ℕ) (t : Memory.State),
      memoryCost (Pure.pure x) t = 0 := fun _ _ => rfl
  have hv : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (defillFinish ![nodeBase, curId, cId])) := by
    dsimp only [defillFinish]
    simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    refine validHistory_read_bind (by omega) (validHistory_read_bind (by omega) ?_)
    rw [h6, h7]
    by_cases hleaf : cLeft = 0 ∧ cRight = 0
    · have hlc : (cLeft = 0 ∧ cRight = 0) = True := eq_true hleaf
      simp only [hlc, ↓reduceIte]
      refine validHistory_read_bind (by omega) ?_
      rw [hnr]
      exact validHistory_write_bind (by omega) hnr_fit
        (validHistory_write_bind (by dsimp only; omega) h0_fit (validHistory_pure w _ _))
    · have hlc : (cLeft = 0 ∧ cRight = 0) = False := eq_false hleaf
      simp only [hlc, ↓reduceIte]
      exact validHistory_write_bind (by omega) hcur_fit (validHistory_pure w _ _)
  have hs_eq : (Memory.spec 0).clientState s (defillFinish ![nodeBase, curId, cId]) =
      if cLeft = 0 ∧ cRight = 0 then
        let s₁ : Memory.State := ⟨Function.update s.mem (nodeBase + 12 * curId + 6) nr, s.frontier⟩
        ⟨Function.update s₁.mem (nodeBase + 12 * curId + 7) 0, s₁.frontier⟩
      else
        ⟨Function.update s.mem (nodeBase + 12 * cId + 8) curId, s.frontier⟩ := by
    dsimp only [defillFinish]
    simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    rw [clientState_bind_read, h6, clientState_bind_read, h7]
    by_cases hleaf : cLeft = 0 ∧ cRight = 0
    · have hlc : (cLeft = 0 ∧ cRight = 0) = True := eq_true hleaf
      simp only [hlc, ↓reduceIte]
      rw [clientState_bind_read, hnr]
      rfl
    · have hlc : (cLeft = 0 ∧ cRight = 0) = False := eq_false hleaf
      simp only [hlc, ↓reduceIte]
      rfl
  have hres_eq : (Memory.spec 0).clientResult s (defillFinish ![nodeBase, curId, cId]) =
      if cLeft = 0 ∧ cRight = 0 then curId else cId := by
    dsimp only [defillFinish]
    simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    rw [clientResult_bind_read, h6, clientResult_bind_read, h7]
    by_cases hleaf : cLeft = 0 ∧ cRight = 0
    · have hlc : (cLeft = 0 ∧ cRight = 0) = True := eq_true hleaf
      simp only [hlc, ↓reduceIte, clientResult_bind_read, hnr, clientResult_bind_write, hcr_pure]
    · have hlc : (cLeft = 0 ∧ cRight = 0) = False := eq_false hleaf
      simp only [hlc, ↓reduceIte, clientResult_bind_write, hcr_pure]
  have hm_eq : memoryCost (defillFinish ![nodeBase, curId, cId]) s =
      if cLeft = 0 ∧ cRight = 0 then 5 else 3 := by
    dsimp only [defillFinish]
    simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read, h6,
      memoryCost_bind', memoryCost_read, clientResult_read, clientState_read, h7]
    by_cases hleaf : cLeft = 0 ∧ cRight = 0
    · have hlc : (cLeft = 0 ∧ cRight = 0) = True := eq_true hleaf
      simp only [hlc, ↓reduceIte, memoryCost_bind', memoryCost_read, memoryCost_write, hmc_pure]
    · have hlc : (cLeft = 0 ∧ cRight = 0) = False := eq_false hleaf
      simp only [hlc, ↓reduceIte, memoryCost_bind', memoryCost_write, hmc_pure]
  have hfr_eq : ((Memory.spec 0).clientState s (defillFinish ![nodeBase, curId, cId])).frontier =
      s.frontier := by
    rw [hs_eq]
    split_ifs <;> rfl
  refine ⟨hv, hfr_eq, ?_⟩
  by_cases hleaf : cLeft = 0 ∧ cRight = 0
  · have hlc : (cLeft = 0 ∧ cRight = 0) = True := eq_true hleaf
    simp only [hlc, ↓reduceIte, hm_eq, hres_eq, hs_eq]
    refine ⟨by omega, trivial, ?_, ?_, fun a ha6 ha7 => ?_⟩
    · rw [Function.update_of_ne (by omega), Function.update_self]
    · rw [Function.update_self]
    · rw [Function.update_of_ne ha7, Function.update_of_ne ha6]
  · have hlc : (cLeft = 0 ∧ cRight = 0) = False := eq_false hleaf
    simp only [hlc, ↓reduceIte, hm_eq, hres_eq, hs_eq]
    refine ⟨by omega, trivial, ?_, fun a ha8 => ?_⟩
    · rw [Function.update_self]
    · rw [Function.update_of_ne ha8]

private theorem zipCurValid_items_ne_empty_of_not_cond {rt lb : ℕ} {cur : SHTree}
    (hval : ZipCurValid rt lb cur)
    (hnot : ¬ (cur.items.length < targetSize rt cur.rank ∧ (cur.left.isSome ∨ cur.right.isSome))) :
    cur.items ≠ [] ∧
    (cur.left.isSome ∨ cur.right.isSome → targetSize rt cur.rank ≤ cur.items.length) := by
  have hpos := targetSize_pos rt cur.rank
  by_cases hne : cur.items = []
  · have hch := hval.2.2.2.2.1 hne
    rw [hne, List.length_nil] at hnot
    exact absurd ⟨hpos, hch⟩ hnot
  · refine ⟨hne, fun hch => ?_⟩
    by_contra hlt
    exact hnot ⟨Nat.lt_of_not_le hlt, hch⟩

private theorem zipFrameRep_replace_cur {rt itemBase nodeBase : ℕ} {mem₁ mem₂ : ℕ → ℕ}
    {c₁ c₂ : SHTree} {f : ZipFrame}
    (hid : c₁.rootId = c₂.rootId)
    (hnode : ∀ id ∈ f.id :: f.sibling.elim [] SHTree.nodeIds,
      ∀ j < 8, mem₁ (nodeBase + 12 * id + j) = mem₂ (nodeBase + 12 * id + j))
    (hitem : ∀ it ∈ f.items ++ f.sibling.elim [] SHTree.allItems,
      ∀ j < 3, mem₁ (itemBase + 3 * it.id + j) = mem₂ (itemBase + 3 * it.id + j))
    (hrep : zipFrameRep rt itemBase nodeBase mem₁ c₁ f) :
    zipFrameRep rt itemBase nodeBase mem₂ c₂ f := by
  rcases hrep with ⟨hfid, h0, h1, h2, h3, h45, h6, h7, hsib⟩
  have hn := hnode f.id (by simp)
  have hitems : ItemListRep itemBase mem₂ (mem₂ (nodeBase + 12 * f.id + 4))
      (mem₂ (nodeBase + 12 * f.id + 5)) f.items := by
    rw [← hn 4 (by decide), ← hn 5 (by decide)]
    exact ItemListRep.congr (fun it hit => hitem it (by simp [hit])) h45
  refine ⟨hfid, ?_, ?_, ?_, ?_, hitems, ?_, ?_, ?_⟩
  · simpa using (hn 0 (by decide)).symm.trans h0
  · rw [← hn 1 (by decide)]; exact h1
  · rw [← hn 2 (by decide)]; exact h2
  · rw [← hn 3 (by decide)]; exact h3
  · rw [← hn 6 (by decide), ← hid]; exact h6
  · rw [← hn 7 (by decide)]; exact h7
  · intro c hc
    refine TreeMemRep.congr
      (fun nid hnid => hnode nid (by simp [hc, hnid]))
      (fun it hit => hitem it (by
        simp only [hc, List.mem_append, Option.elim_some]
        right
        simpa [SHTree.allItems] using hit))
      (hsib c hc)

private theorem ZipFramesRep_replace_cur {rt itemBase nodeBase : ℕ} {mem₁ mem₂ : ℕ → ℕ}
    {c₁ c₂ : SHTree} {ctx : List ZipFrame} {lb : ℕ}
    (hid : c₁.rootId = c₂.rootId) (hrk : c₁.rank = c₂.rank)
    (hc8 : mem₁ (nodeBase + 12 * c₁.rootId + 8) = mem₂ (nodeBase + 12 * c₂.rootId + 8))
    (hnode : ∀ id ∈ ctx.flatMap (fun f => f.id :: f.sibling.elim [] SHTree.nodeIds),
      ∀ j < 9, mem₁ (nodeBase + 12 * id + j) = mem₂ (nodeBase + 12 * id + j))
    (hitem : ∀ it ∈ ctx.flatMap (fun f => f.items ++ f.sibling.elim [] SHTree.allItems),
      ∀ j < 3, mem₁ (itemBase + 3 * it.id + j) = mem₂ (itemBase + 3 * it.id + j))
    (hrep : ZipFramesRep rt itemBase nodeBase mem₁ c₁ ctx lb) :
    ZipFramesRep rt itemBase nodeBase mem₂ c₂ ctx lb := by
  induction ctx generalizing c₁ c₂ lb with
  | nil =>
    rcases hrep with ⟨h8, rfl⟩
    exact ⟨hc8.symm.trans h8, rfl⟩
  | cons f rest ih =>
    rcases hrep with ⟨h8, hne, hcap, hle, hk8, hcrk, hsib, hfrep, rfl, lb', hlb', hrest⟩
    have hf_node : ∀ id ∈ f.id :: f.sibling.elim [] SHTree.nodeIds,
        ∀ j < 8, mem₁ (nodeBase + 12 * id + j) = mem₂ (nodeBase + 12 * id + j) :=
      fun id hid' j hj => hnode id (List.mem_flatMap.mpr ⟨f, List.mem_cons_self, hid'⟩) j
        (by omega)
    have hf_item : ∀ it ∈ f.items ++ f.sibling.elim [] SHTree.allItems,
        ∀ j < 3, mem₁ (itemBase + 3 * it.id + j) = mem₂ (itemBase + 3 * it.id + j) :=
      fun it hit' j hj => hitem it (List.mem_flatMap.mpr ⟨f, List.mem_cons_self, hit'⟩) j hj
    have hplug8 : mem₁ (nodeBase + 12 * (zipPlug f c₁).rootId + 8) =
        mem₂ (nodeBase + 12 * (zipPlug f c₂).rootId + 8) :=
      hnode f.id (by simp) 8 (by decide)
    have hrest' := ih (c₁ := zipPlug f c₁) (c₂ := zipPlug f c₂) rfl rfl hplug8
      (fun id hid' => hnode id (by
        rcases List.mem_flatMap.mp hid' with ⟨g, hg, hmg⟩
        exact List.mem_flatMap.mpr ⟨g, List.mem_cons_of_mem _ hg, hmg⟩))
      (fun it hit' => hitem it (by
        rcases List.mem_flatMap.mp hit' with ⟨g, hg, hmg⟩
        exact List.mem_flatMap.mpr ⟨g, List.mem_cons_of_mem _ hg, hmg⟩)) hrest
    exact ⟨hc8.symm.trans h8, hne, hcap, hle, hk8, by rw [← hrk]; exact hcrk, hsib,
      zipFrameRep_replace_cur hid hf_node hf_item hfrep, rfl, lb', hlb', hrest'⟩

private def DefillStepPost (rt w itemBase nodeBase : ℕ) (t₀ cur : SHTree)
    (ctx : List ZipFrame) (s : Memory.State) : Prop :=
  let d : Fin 3 → ℕ := ![itemBase, nodeBase, cur.rootId]
  (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (defillStep d)) ∧
  ∃ (cur?' : Option SHTree) (ctx' : List ZipFrame),
    let res := (Memory.spec 0).clientResult s (defillStep d)
    let s' := (Memory.spec 0).clientState s (defillStep d)
    res = cur?'.elim 0 SHTree.rootId ∧
    s'.frontier = s.frontier ∧
    (∀ a, s'.mem a ≠ s.mem a →
      (∃ id ∈ t₀.nodeIds, ∃ j < 9, a = nodeBase + 12 * id + j) ∨
      (∃ it ∈ t₀.allItems, a = itemBase + 3 * it.id + 2)) ∧
    5 ≤ memoryCost (defillStep d) s ∧
    match cur?' with
    | none =>
        ZipInv rt w itemBase nodeBase t₀ none [] s' ∧
        (memoryCost (defillStep d) s : ℚ) + cur.phi rt ≤ zipPhi rt (some cur) ctx ∧
        ctx = [] ∧
        cur.rootId = t₀.rootId ∧ cur.rank = t₀.rank ∧ cur.Valid rt 0 ∧
        (cur.left.isSome ∨ cur.right.isSome → targetSize rt cur.rank ≤ cur.items.length) ∧
        (t₀.items ≠ [] → t₀.ckey ≤ cur.ckey) ∧
        cur.nodeIds.Nodup ∧ (∀ id ∈ cur.nodeIds, id ∈ t₀.nodeIds) ∧
        (∀ id ∈ t₀.nodeIds, id ∉ cur.nodeIds → s'.mem (nodeBase + 12 * id + 4) = 0) ∧
        (∀ k, cur.countRank k ≤ t₀.countRank k) ∧
        cur.allItems.Perm t₀.allItems ∧
        (∀ p ∈ cur.allEntries, ∃ c₀, (p.1, c₀) ∈ t₀.allEntries ∧ c₀ ≤ p.2) ∧
        TreeMemRep rt itemBase nodeBase s'.mem cur ∧
        s'.mem (nodeBase + 12 * cur.rootId + 8) = 0
    | some cur' =>
        ZipInv rt w itemBase nodeBase t₀ (some cur') ctx' s' ∧
        (memoryCost (defillStep d) s : ℚ) + zipPhi rt (some cur') ctx' ≤ zipPhi rt (some cur) ctx

private structure DefillCurInfo (rt itemBase nodeBase : ℕ) (t₀ cur : SHTree)
    (s : Memory.State) : Prop where
  sub : ∀ id ∈ cur.nodeIds, id ∈ t₀.nodeIds
  nd : cur.nodeIds.Nodup
  items_sub : ∀ it ∈ cur.allItems, it ∈ t₀.allItems
  item_nd : cur.itemIds.Nodup
  root_lt : nodeBase + 12 * cur.rootId + 11 < s.frontier
  sz : s.mem (nodeBase + 12 * cur.rootId + 3) = cur.items.length
  tgt : s.mem (nodeBase + 12 * cur.rootId + 2) = targetSize rt cur.rank
  l : s.mem (nodeBase + 12 * cur.rootId + 6) = cur.left.elim 0 SHTree.rootId
  r : s.mem (nodeBase + 12 * cur.rootId + 7) = cur.right.elim 0 SHTree.rootId
  l0_iff : s.mem (nodeBase + 12 * cur.rootId + 6) ≠ 0 ↔ cur.left.isSome
  r0_iff : s.mem (nodeBase + 12 * cur.rootId + 7) ≠ 0 ↔ cur.right.isSome

private theorem defillCurInfo_of_zipInv {rt w itemBase nodeBase : ℕ} {t₀ cur : SHTree}
    {ctx : List ZipFrame} {s : Memory.State}
    (hinv : ZipInv rt w itemBase nodeBase t₀ (some cur) ctx s) :
    DefillCurInfo rt itemBase nodeBase t₀ cur s := by
  rcases hinv with ⟨_, _, hn_lt, _, _, _, _, hnd, hsub, _, hid_nd,
    _, hperm, _, _, hcur_mem, _, _, _⟩
  have hcur_sub : ∀ id ∈ cur.nodeIds, id ∈ t₀.nodeIds := fun id hid =>
    hsub id (zipRebuild_nodeIds_sub cur ctx id hid)
  have hcur_nd : cur.nodeIds.Nodup := by
    have hp := (zipRebuild_nodeIds_perm cur ctx).nodup_iff.mp hnd
    exact (List.nodup_append.mp hp).1
  have hcur_items_sub : ∀ it ∈ cur.allItems, it ∈ t₀.allItems := fun it hit => by
    have hperm' := (zipRebuild_allEntries_perm cur ctx).map Prod.fst
    rw [List.map_append] at hperm'
    exact hperm.mem_iff.mp (hperm'.mem_iff.mpr (List.mem_append_left _ hit))
  have hcur_item_nd : cur.itemIds.Nodup := by
    have hp := ((zipRebuild_allEntries_perm cur ctx).map Prod.fst).map SHItem.id
    have hp2 := hp.nodup_iff.mp hid_nd
    rw [List.map_append, List.map_append] at hp2
    simpa [SHTree.itemIds, SHTree.allItems] using (List.nodup_append.mp hp2).1
  have hcur_root_lt : nodeBase + 12 * cur.rootId + 11 < s.frontier :=
    hn_lt cur.rootId (hcur_sub cur.rootId cur.rootId_mem_nodeIds)
  have hcur_sz : s.mem (nodeBase + 12 * cur.rootId + 3) = cur.items.length :=
    hcur_mem.size_eq
  have hcur_tgt : s.mem (nodeBase + 12 * cur.rootId + 2) = targetSize rt cur.rank :=
    hcur_mem.target_eq
  have hcur_l : s.mem (nodeBase + 12 * cur.rootId + 6) = cur.left.elim 0 SHTree.rootId :=
    hcur_mem.left_eq
  have hcur_r : s.mem (nodeBase + 12 * cur.rootId + 7) = cur.right.elim 0 SHTree.rootId :=
    hcur_mem.right_eq
  have hcur_l0_iff : s.mem (nodeBase + 12 * cur.rootId + 6) ≠ 0 ↔ cur.left.isSome := by
    rw [hcur_l]
    cases hl_opt : cur.left with
    | none => simp
    | some c => simp [(hcur_mem.left_mem c hl_opt).rootId_ne]
  have hcur_r0_iff : s.mem (nodeBase + 12 * cur.rootId + 7) ≠ 0 ↔ cur.right.isSome := by
    rw [hcur_r]
    cases hr_opt : cur.right with
    | none => simp
    | some c => simp [(hcur_mem.right_mem c hr_opt).rootId_ne]
  exact ⟨hcur_sub, hcur_nd, hcur_items_sub, hcur_item_nd, hcur_root_lt, hcur_sz, hcur_tgt,
    hcur_l, hcur_r, hcur_l0_iff, hcur_r0_iff⟩


private theorem SHTree.Valid.replace_lb {rt lb₁ lb₂ : ℕ} {t : SHTree} (h : lb₂ ≤ t.ckey)
    (ht : t.Valid rt lb₁) : t.Valid rt lb₂ := by
  cases ht with
  | node hne hcap _ hle h8 hhalf hl_rk hl_v hr_rk hr_v =>
    exact .node hne hcap h hle h8 hhalf hl_rk hl_v hr_rk hr_v

private theorem zipRebuild_ckey_of_cons (a b : SHTree) (g : ZipFrame) (rest : List ZipFrame) :
    (zipRebuild (zipPlug g a) rest).ckey = (zipRebuild (zipPlug g b) rest).ckey := by
  induction rest generalizing g a b with
  | nil => rfl
  | cons h rest ih =>
    simp only [zipRebuild]
    exact ih (zipPlug g a) (zipPlug g b) h

private structure DefillStepPSRes (rt w itemBase nodeBase : ℕ) (t₀ cur c : SHTree)
    (sib : Option SHTree) (s s₁ s₂ s₃ : Memory.State) : Prop where
  fr_pick : s₁.frontier = s.frontier
  mem_pick : ∀ a, a ≠ nodeBase + 12 * cur.rootId + 6 →
    a ≠ nodeBase + 12 * cur.rootId + 7 → s₁.mem a = s.mem a
  csib : (cur.left = some c ∧ cur.right = sib) ∨ (cur.right = some c ∧ cur.left = sib)
  c_le_sib : ∀ sc, sib = some sc → c.ckey ≤ sc.ckey
  cur_ne_c : cur.rootId ≠ c.rootId
  c_val : c.rank + 1 = cur.rank ∧ c.Valid rt cur.ckey
  c_mem : TreeMemRep rt itemBase nodeBase s.mem c
  cur1_mem : TreeMemRep rt itemBase nodeBase s₁.mem
    (.node cur.rootId cur.rank cur.ckey cur.items (some c) sib)
  v_sp : (Memory.spec w).ValidHistory s₁
    ((Memory.spec w).clientHistory s₁
      (defillSplice ![itemBase, nodeBase, cur.rootId, c.rootId, cur.items.length]))
  m_sp : memoryCost
    (defillSplice ![itemBase, nodeBase, cur.rootId, c.rootId, cur.items.length]) s₁ ≤ 13
  fr_sp : s₂.frontier = s₁.frontier
  mem_sp : ∀ a, a ≠ nodeBase + 12 * cur.rootId → a ≠ nodeBase + 12 * cur.rootId + 3 →
    a ≠ nodeBase + 12 * cur.rootId + 4 → a ≠ nodeBase + 12 * cur.rootId + 5 →
    a ≠ nodeBase + 12 * c.rootId + 3 → a ≠ nodeBase + 12 * c.rootId + 4 →
    a ≠ nodeBase + 12 * c.rootId + 5 →
    (cur.items = [] ∨ a ≠ itemBase + 3 * s₁.mem (nodeBase + 12 * cur.rootId + 5) + 2) →
    s₂.mem a = s₁.mem a
  s2_0 : s₂.mem (nodeBase + 12 * cur.rootId) = c.ckey
  s2_3 : s₂.mem (nodeBase + 12 * cur.rootId + 3) = (cur.items ++ c.items).length
  s2_45 : ItemListRep itemBase s₂.mem
    (s₂.mem (nodeBase + 12 * cur.rootId + 4))
    (s₂.mem (nodeBase + 12 * cur.rootId + 5))
    (cur.items ++ c.items)
  s2_c3 : s₂.mem (nodeBase + 12 * c.rootId + 3) = 0
  s2_c4 : s₂.mem (nodeBase + 12 * c.rootId + 4) = 0
  s2_c5 : s₂.mem (nodeBase + 12 * c.rootId + 5) = 0
  wf3 : Memory.WellFormed w s₃
  fr_fin : s₃.frontier = s₂.frontier
  fin_cases :
    if c.left.elim 0 SHTree.rootId = 0 ∧ c.right.elim 0 SHTree.rootId = 0 then
      memoryCost (defillStep ![itemBase, nodeBase, cur.rootId]) s ≤ 26 ∧
      (Memory.spec 0).clientResult s (defillStep ![itemBase, nodeBase, cur.rootId]) =
        cur.rootId ∧
      s₃.mem (nodeBase + 12 * cur.rootId + 6) = sib.elim 0 SHTree.rootId ∧
      s₃.mem (nodeBase + 12 * cur.rootId + 7) = 0 ∧
      ∀ a, a ≠ nodeBase + 12 * cur.rootId + 6 → a ≠ nodeBase + 12 * cur.rootId + 7 →
        s₃.mem a = s₂.mem a
    else
      memoryCost (defillStep ![itemBase, nodeBase, cur.rootId]) s ≤ 24 ∧
      (Memory.spec 0).clientResult s (defillStep ![itemBase, nodeBase, cur.rootId]) =
        c.rootId ∧
      s₃.mem (nodeBase + 12 * c.rootId + 8) = cur.rootId ∧
      ∀ a, a ≠ nodeBase + 12 * c.rootId + 8 → s₃.mem a = s₂.mem a
  v_step : (Memory.spec w).ValidHistory s
    ((Memory.spec w).clientHistory s (defillStep ![itemBase, nodeBase, cur.rootId]))
  cost_ge5 : 5 ≤ memoryCost (defillStep ![itemBase, nodeBase, cur.rootId]) s
  cap_sum : (cur.items ++ c.items).length ≤ sizeCap rt cur.rank
  k8_cur' : cur.rank ≤ rt → ∀ it ∈ cur.items ++ c.items, it.origKey = c.ckey
  le_cur' : ∀ it ∈ cur.items ++ c.items, it.origKey ≤ c.ckey
  cur_all_perm :
    (SHTree.node cur.rootId cur.rank cur.ckey cur.items (some c) sib).allItems.Perm cur.allItems ∧
    (∀ p ∈ (SHTree.node cur.rootId cur.rank cur.ckey cur.items (some c) sib).allEntries,
      p ∈ cur.allEntries) ∧
    (SHTree.node cur.rootId cur.rank cur.ckey cur.items (some c) sib).nodeIds.Perm cur.nodeIds ∧
    (∀ k, (SHTree.node cur.rootId cur.rank cur.ckey cur.items (some c) sib).countRank k =
      cur.countRank k) ∧
    (SHTree.node cur.rootId cur.rank cur.ckey cur.items (some c) sib).phi rt = cur.phi rt
  sib_sub_node : ∀ nid ∈ sib.elim [] SHTree.nodeIds,
    nid ≠ cur.rootId ∧ nid ≠ c.rootId ∧ nid ∈ cur.nodeIds
  sib_sub_item : ∀ it ∈ sib.elim [] SHTree.allItems,
    it ∉ cur.items ∧ it ∉ c.items ∧ it ∈ cur.allItems
  s2_not_sib : ∀ nid ∈ sib.elim [] SHTree.nodeIds, ∀ j < 12,
    s₂.mem (nodeBase + 12 * nid + j) = s.mem (nodeBase + 12 * nid + j)
  s2_not_sib_item : ∀ it ∈ sib.elim [] SHTree.allItems, ∀ j < 3,
    s₂.mem (itemBase + 3 * it.id + j) = s.mem (itemBase + 3 * it.id + j)
  s_step : (Memory.spec 0).clientState s (defillStep ![itemBase, nodeBase, cur.rootId]) = s₃
  c_in_cur : c.rootId ∈ cur.nodeIds
  s2_frame : ∀ a, s₂.mem a ≠ s.mem a →
    (∃ id ∈ cur.nodeIds, ∃ j < 8, a = nodeBase + 12 * id + j) ∨
    (∃ it ∈ cur.items, a = itemBase + 3 * it.id + 2)

private theorem defillStep_ps_spec {rt w itemBase nodeBase : ℕ} {t₀ cur : SHTree}
    {ctx : List ZipFrame} {s : Memory.State}
    (hinv : ZipInv rt w itemBase nodeBase t₀ (some cur) ctx s)
    (hinfo : DefillCurInfo rt itemBase nodeBase t₀ cur s)
    (hc_cond : cur.items.length < targetSize rt cur.rank ∧
      (cur.left.isSome ∨ cur.right.isSome)) :
    ∃ c sib s₁ s₂ s₃, DefillStepPSRes rt w itemBase nodeBase t₀ cur c sib s s₁ s₂ s₃ := by
  rcases hinv with ⟨h16, hmem, hn_lt, hi_lt, hdisj, _, _, _, _, _, _,
    _, _, _, _, hcur_mem, _, hval, _⟩
  rcases hinfo with ⟨hcur_sub, hcur_nd, hcur_items_sub, hcur_item_nd, hcur_root_lt,
    hcur_sz, hcur_tgt, hcur_l, hcur_r, hcur_l0_iff, hcur_r0_iff⟩
  have hcond_mem : s.mem (nodeBase + 12 * cur.rootId + 3) <
      s.mem (nodeBase + 12 * cur.rootId + 2) ∧
      (s.mem (nodeBase + 12 * cur.rootId + 6) ≠ 0 ∨
        s.mem (nodeBase + 12 * cur.rootId + 7) ≠ 0) := by
    rw [hcur_sz, hcur_tgt, hcur_l0_iff, hcur_r0_iff]; exact hc_cond
  have hpick := defillPickChild_spec h16 hmem hcur_mem hc_cond.2
    (fun id hid => hn_lt id (hcur_sub id hid)) hcur_l hcur_r
  rcases hpick with ⟨hv_pick, hm_pick, hfr_pick, hmem_pick, c, sib, hcsib, hres_pick,
    hs1_6, hs1_7, hc_le_sib⟩
  obtain ⟨s₁, hs₁_eq⟩ : ∃ s₁, s₁ = (Memory.spec 0).clientState s (defillPickChild ![nodeBase,
      cur.rootId, s.mem (nodeBase + 12 * cur.rootId + 6),
      s.mem (nodeBase + 12 * cur.rootId + 7)]) := ⟨_, rfl⟩
  rw [← hs₁_eq] at hfr_pick hmem_pick hs1_6 hs1_7
  have hwf₁ : Memory.WellFormed w s₁ := by
    rw [hs₁_eq]; exact wellFormed_clientState hmem hv_pick
  have hc_in_cur : c.rootId ∈ cur.nodeIds := by
    cases cur with
    | node id r ck items l r' =>
      rcases hcsib with ⟨hl, _⟩ | ⟨hr, _⟩ <;>
        dsimp only [SHTree.left, SHTree.right] at * <;> subst_vars <;>
        simp [SHTree.rootId_mem_nodeIds]
  have hcur_ne_c : cur.rootId ≠ c.rootId := by
    cases cur with
    | node id r ck items l r' =>
      have hnd_cur := SHTree.nodeIds_head_not_mem hcur_nd
      rcases hcsib with ⟨hl, _⟩ | ⟨hr, _⟩
      · dsimp only [SHTree.left] at hl; subst hl
        intro heq
        dsimp only [SHTree.rootId] at heq
        exact hnd_cur (List.mem_append_left _ (heq ▸ c.rootId_mem_nodeIds))
      · dsimp only [SHTree.right] at hr; subst hr
        intro heq
        dsimp only [SHTree.rootId] at heq
        exact hnd_cur (List.mem_append_right _ (heq ▸ c.rootId_mem_nodeIds))
  have hc_val : c.rank + 1 = cur.rank ∧ c.Valid rt cur.ckey := by
    rcases hcsib with ⟨hl, _⟩ | ⟨hr, _⟩
    · exact hval.2.2.2.2.2.1 c hl
    · exact hval.2.2.2.2.2.2 c hr
  have hc_mem : TreeMemRep rt itemBase nodeBase s.mem c := by
    rcases hcsib with ⟨hl, _⟩ | ⟨hr, _⟩
    · exact hcur_mem.left_mem c hl
    · exact hcur_mem.right_mem c hr
  have hcur₁_mem : TreeMemRep rt itemBase nodeBase s₁.mem
      (.node cur.rootId cur.rank cur.ckey cur.items (some c) sib) := by
    cases cur with
    | node id r ck items l r' =>
      rcases hcur_mem with ⟨hid, h0, h1, h2, h3, h45, _, _, hl, hr⟩
      dsimp only [SHTree.rootId] at hmem_pick hs1_6 hs1_7
      have hc_sub_cur : ∀ nid ∈ c.nodeIds, nid ≠ id := by
        intro nid hnid heq; subst heq
        have hnd' := SHTree.nodeIds_head_not_mem hcur_nd
        rcases hcsib with ⟨rfl, _⟩ | ⟨rfl, _⟩
        · exact hnd' (List.mem_append_left _ hnid)
        · exact hnd' (List.mem_append_right _ hnid)
      have hc_mem₁ : TreeMemRep rt itemBase nodeBase s₁.mem c := by
        refine TreeMemRep.congr (fun nid hnid j hj => ?_) (fun it hit j hj => ?_) hc_mem
        · have hne := hc_sub_cur nid hnid
          exact (hmem_pick _ (by omega) (by omega)).symm
        · have hit' := hcur_items_sub it (by
            rcases hcsib with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp [SHTree.allItems_node, hit])
          have hd6 := hdisj id (hcur_sub id (by simp)) it hit' 6 (by decide) j hj
          have hd7 := hdisj id (hcur_sub id (by simp)) it hit' 7 (by decide) j hj
          exact (hmem_pick _ hd6.symm hd7.symm).symm
      have h45₁ : ItemListRep itemBase s₁.mem (s₁.mem (nodeBase + 12 * id + 4))
          (s₁.mem (nodeBase + 12 * id + 5)) items := by
        rw [hmem_pick _ (by omega) (by omega), hmem_pick _ (by omega) (by omega)]
        refine ItemListRep.congr (fun it hit j hj => ?_) h45
        have hit' := hcur_items_sub it (by simp [SHTree.allItems_node, hit])
        have hd6 := hdisj id (hcur_sub id (by simp)) it hit' 6 (by decide) j hj
        have hd7 := hdisj id (hcur_sub id (by simp)) it hit' 7 (by decide) j hj
        exact (hmem_pick _ hd6.symm hd7.symm).symm
      refine .node hid ?_ ?_ ?_ ?_ h45₁ hs1_6 hs1_7 (fun x hx => ?_) (fun x hx => ?_)
      · rw [hmem_pick _ (by omega) (by omega)]; exact h0
      · rw [hmem_pick _ (by omega) (by omega)]; exact h1
      · rw [hmem_pick _ (by omega) (by omega)]; exact h2
      · rw [hmem_pick _ (by omega) (by omega)]; exact h3
      · cases hx; exact hc_mem₁
      · rcases hcsib with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · dsimp only [SHTree.right] at hx
          refine TreeMemRep.congr (fun nid hnid j hj => ?_) (fun it hit j hj => ?_)
            (hr x hx)
          · have hne : nid ≠ id := by
              intro heq; subst heq
              exact SHTree.nodeIds_head_not_mem hcur_nd
                (List.mem_append_right _ (by simp [hx, hnid]))
            exact (hmem_pick _ (by omega) (by omega)).symm
          · have hit' := hcur_items_sub it (by simp [SHTree.allItems_node, hx, hit])
            exact (hmem_pick _ (hdisj id (hcur_sub id (by simp)) it hit' 6 (by decide) j hj).symm
              (hdisj id (hcur_sub id (by simp)) it hit' 7 (by decide) j hj).symm).symm
        · dsimp only [SHTree.left] at hx
          refine TreeMemRep.congr (fun nid hnid j hj => ?_) (fun it hit j hj => ?_)
            (hl x hx)
          · have hne : nid ≠ id := by
              intro heq; subst heq
              exact SHTree.nodeIds_head_not_mem hcur_nd
                (List.mem_append_left _ (by simp [hx, hnid]))
            exact (hmem_pick _ (by omega) (by omega)).symm
          · have hit' := hcur_items_sub it (by simp [SHTree.allItems_node, hx, hit])
            exact (hmem_pick _ (hdisj id (hcur_sub id (by simp)) it hit' 6 (by decide) j hj).symm
              (hdisj id (hcur_sub id (by simp)) it hit' 7 (by decide) j hj).symm).symm
  have hc_mem₁ : TreeMemRep rt itemBase nodeBase s₁.mem c := hcur₁_mem.left_mem c rfl
  have hcur_item_list_nd : (cur.items.map SHItem.id).Nodup := by
    have hid_eq : cur.itemIds = cur.items.map SHItem.id ++
        (cur.left.elim [] SHTree.itemIds ++ cur.right.elim [] SHTree.itemIds) := by
      cases cur
      dsimp only [SHTree.items, SHTree.left, SHTree.right]
      simp [SHTree.itemIds_node, List.append_assoc]
    rw [hid_eq] at hcur_item_nd
    exact (list_nodup_append_disj hcur_item_nd).1
  have hc_item_nd : (c.items.map SHItem.id).Nodup := by
    have hc_ids_eq : c.itemIds = c.items.map SHItem.id ++
        (c.left.elim [] SHTree.itemIds ++ c.right.elim [] SHTree.itemIds) := by
      cases c
      dsimp only [SHTree.items, SHTree.left, SHTree.right]
      simp [SHTree.itemIds_node, List.append_assoc]
    have hsub_c : c.itemIds.Nodup := by
      cases cur with
      | node id r ck items l r' =>
        have hid_eq : SHTree.itemIds (.node id r ck items l r') =
            items.map SHItem.id ++ l.elim [] SHTree.itemIds ++ r'.elim [] SHTree.itemIds :=
          SHTree.itemIds_node id r ck items l r'
        rw [hid_eq] at hcur_item_nd
        rcases hcsib with ⟨rfl, _⟩ | ⟨rfl, _⟩
        · exact (list_nodup_append_disj (list_nodup_append_disj hcur_item_nd).1).2.1
        · exact (list_nodup_append_disj hcur_item_nd).2.1
    rw [hc_ids_eq] at hsub_c
    exact (list_nodup_append_disj hsub_c).1
  have hcur_c_disj : ∀ x ∈ cur.items, ∀ y ∈ c.items, x.id ≠ y.id := by
    intro x hx y hy heq
    cases cur with
    | node id r ck items l r' =>
      have hid_eq : SHTree.itemIds (.node id r ck items l r') =
          items.map SHItem.id ++ l.elim [] SHTree.itemIds ++ r'.elim [] SHTree.itemIds :=
        SHTree.itemIds_node id r ck items l r'
      rw [hid_eq] at hcur_item_nd
      dsimp only [SHTree.items] at hx
      have hx_m : x.id ∈ items.map SHItem.id := List.mem_map_of_mem hx
      have hy_c : y.id ∈ c.itemIds := by
        cases c; dsimp only [SHTree.items] at hy
        rw [SHTree.itemIds_node]
        exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hy))
      rcases hcsib with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · have hdis := (list_nodup_append_disj (list_nodup_append_disj hcur_item_nd).1).2.2
        exact hdis x.id hx_m (heq ▸ hy_c)
      · have hdis := (list_nodup_append_disj hcur_item_nd).2.2
        exact hdis x.id (List.mem_append_left _ hx_m) (heq ▸ hy_c)
  have hc_lt : nodeBase + 12 * c.rootId + 11 < s₁.frontier := by
    rw [hfr_pick]
    exact hn_lt c.rootId (hcur_sub c.rootId hc_in_cur)
  have hi_cur₁ : ∀ it ∈ cur.items, itemBase + 3 * it.id + 2 < s₁.frontier := fun it hit => by
    rw [hfr_pick]
    exact hi_lt it (hcur_items_sub it (by
      cases cur; dsimp only [SHTree.items] at hit; simp [SHTree.allItems_node, hit]))
  have hi_c₁ : ∀ it ∈ c.items, itemBase + 3 * it.id + 2 < s₁.frontier := fun it hit => by
    rw [hfr_pick]
    have hit_c : it ∈ c.allItems := by
      cases c; dsimp only [SHTree.items] at hit; simp [SHTree.allItems_node, hit]
    exact hi_lt it (hcur_items_sub it (by
      cases cur with
      | node _ _ _ _ _ _ =>
        rcases hcsib with ⟨hl, _⟩ | ⟨hr, _⟩
        · dsimp only [SHTree.left] at hl; simp [SHTree.allItems_node, hl, hit_c]
        · dsimp only [SHTree.right] at hr; simp [SHTree.allItems_node, hr, hit_c]))
  have hdisj₁ : ∀ id, id = cur.rootId ∨ id = c.rootId →
      ∀ it ∈ cur.items ++ c.items, ∀ j < 12, ∀ k < 3,
        nodeBase + 12 * id + j ≠ itemBase + 3 * it.id + k := by
    intro id hid it hit j hj k hk
    apply hdisj id _ it _ j hj k hk
    · rcases hid with rfl | rfl
      · exact hcur_sub cur.rootId cur.rootId_mem_nodeIds
      · exact hcur_sub c.rootId hc_in_cur
    · rcases List.mem_append.mp hit with h1 | h2
      · exact hcur_items_sub it (by
          cases cur; dsimp only [SHTree.items] at h1; simp [SHTree.allItems_node, h1])
      · have hit_c : it ∈ c.allItems := by
          cases c; dsimp only [SHTree.items] at h2; simp [SHTree.allItems_node, h2]
        exact hcur_items_sub it (by
          cases cur with
          | node _ _ _ _ _ _ =>
            rcases hcsib with ⟨hl, _⟩ | ⟨hr, _⟩
            · dsimp only [SHTree.left] at hl; simp [SHTree.allItems_node, hl, hit_c]
            · dsimp only [SHTree.right] at hr; simp [SHTree.allItems_node, hr, hit_c])
  have hsp := defillSplice_spec h16 hwf₁ hcur₁_mem hc_mem₁ hc_val.2.items_ne hcur_ne_c
    hcur_item_list_nd hcur_c_disj (hfr_pick.symm ▸ hcur_root_lt) hc_lt hi_cur₁ hi_c₁
    hc_item_nd hdisj₁
  obtain ⟨s₂, hs₂_eq⟩ : ∃ s₂, s₂ = (Memory.spec 0).clientState s₁ (defillSplice ![itemBase,
      nodeBase, cur.rootId, c.rootId, cur.items.length]) := ⟨_, rfl⟩
  have hsp' :
      (Memory.spec w).ValidHistory s₁ ((Memory.spec w).clientHistory s₁
        (defillSplice ![itemBase, nodeBase, cur.rootId, c.rootId, cur.items.length])) ∧
      memoryCost (defillSplice ![itemBase, nodeBase, cur.rootId, c.rootId,
        cur.items.length]) s₁ ≤ 13 ∧
      s₂.frontier = s₁.frontier ∧
      (∀ a, a ≠ nodeBase + 12 * cur.rootId → a ≠ nodeBase + 12 * cur.rootId + 3 →
        a ≠ nodeBase + 12 * cur.rootId + 4 → a ≠ nodeBase + 12 * cur.rootId + 5 →
        a ≠ nodeBase + 12 * c.rootId + 3 → a ≠ nodeBase + 12 * c.rootId + 4 →
        a ≠ nodeBase + 12 * c.rootId + 5 →
        (cur.items = [] ∨
          a ≠ itemBase + 3 * s₁.mem (nodeBase + 12 * cur.rootId + 5) + 2) →
        s₂.mem a = s₁.mem a) ∧
      s₂.mem (nodeBase + 12 * cur.rootId) = c.ckey ∧
      s₂.mem (nodeBase + 12 * cur.rootId + 3) = (cur.items ++ c.items).length ∧
      ItemListRep itemBase s₂.mem (s₂.mem (nodeBase + 12 * cur.rootId + 4))
        (s₂.mem (nodeBase + 12 * cur.rootId + 5)) (cur.items ++ c.items) ∧
      s₂.mem (nodeBase + 12 * c.rootId + 3) = 0 ∧
      s₂.mem (nodeBase + 12 * c.rootId + 4) = 0 ∧
      s₂.mem (nodeBase + 12 * c.rootId + 5) = 0 := by
    rw [hs₂_eq]
    exact hsp
  rcases hsp' with ⟨hv_sp, hm_sp, hfr_sp, hmem_sp, hs2_0, hs2_3, hs2_45, hs2_c3, hs2_c4, hs2_c5⟩
  have hwf₂ : Memory.WellFormed w s₂ := by
    rw [hs₂_eq]; exact wellFormed_clientState hwf₁ hv_sp
  have hcur_fit : Fits w cur.rootId :=
    hmem.fits_of_lt_frontier (Nat.lt_of_le_of_lt (by omega) hcur_root_lt)
  have hs2_c_child : ∀ off, off = 6 ∨ off = 7 →
      s₂.mem (nodeBase + 12 * c.rootId + off) = s₁.mem (nodeBase + 12 * c.rootId + off) := by
    intro off hoff
    apply hmem_sp _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    by_cases hnil : cur.items = []
    · exact Or.inl hnil
    · right
      rcases ItemListRep.tail_mem hnil hcur₁_mem.items_rep with ⟨it_l, hit_l, htl_eq, _⟩
      change s₁.mem (nodeBase + 12 * cur.rootId + 5) = it_l.id at htl_eq
      rw [htl_eq]
      have hit_l' : it_l ∈ cur.items ++ c.items := List.mem_append_left _ hit_l
      rcases hoff with rfl | rfl <;>
        exact hdisj₁ c.rootId (Or.inr rfl) it_l hit_l' _ (by decide) 2 (by decide)
  have hs2_c6 : s₂.mem (nodeBase + 12 * c.rootId + 6) = c.left.elim 0 SHTree.rootId :=
    (hs2_c_child 6 (Or.inl rfl)).trans hc_mem₁.left_eq
  have hs2_c7 : s₂.mem (nodeBase + 12 * c.rootId + 7) = c.right.elim 0 SHTree.rootId :=
    (hs2_c_child 7 (Or.inr rfl)).trans hc_mem₁.right_eq
  have hs2_nr : s₂.mem (nodeBase + 12 * cur.rootId + 7) = sib.elim 0 SHTree.rootId := by
    rw [← hs1_7]
    apply hmem_sp _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    by_cases hnil : cur.items = []
    · exact Or.inl hnil
    · right
      rcases ItemListRep.tail_mem hnil hcur₁_mem.items_rep with ⟨it_l, hit_l, htl_eq, _⟩
      change s₁.mem (nodeBase + 12 * cur.rootId + 5) = it_l.id at htl_eq
      rw [htl_eq]
      have hit_l' : it_l ∈ cur.items ++ c.items := List.mem_append_left _ hit_l
      exact hdisj₁ cur.rootId (Or.inl rfl) it_l hit_l' 7 (by decide) 2 (by decide)
  have hs2_frame : ∀ a, s₂.mem a ≠ s.mem a →
      (∃ id ∈ cur.nodeIds, ∃ j < 8, a = nodeBase + 12 * id + j) ∨
      (∃ it ∈ cur.items, a = itemBase + 3 * it.id + 2) := by
    intro a ha
    by_cases hsp_eq : s₂.mem a = s₁.mem a
    · rw [hsp_eq] at ha
      by_cases ha6 : a = nodeBase + 12 * cur.rootId + 6
      · exact Or.inl ⟨cur.rootId, cur.rootId_mem_nodeIds, 6, by decide, ha6⟩
      · by_cases ha7 : a = nodeBase + 12 * cur.rootId + 7
        · exact Or.inl ⟨cur.rootId, cur.rootId_mem_nodeIds, 7, by decide, ha7⟩
        · exact absurd (hmem_pick a ha6 ha7) ha
    · by_contra hno
      apply hsp_eq
      apply hmem_sp a
        (fun h => hno (Or.inl ⟨cur.rootId, cur.rootId_mem_nodeIds, 0, by decide, h⟩))
        (fun h => hno (Or.inl ⟨cur.rootId, cur.rootId_mem_nodeIds, 3, by decide, h⟩))
        (fun h => hno (Or.inl ⟨cur.rootId, cur.rootId_mem_nodeIds, 4, by decide, h⟩))
        (fun h => hno (Or.inl ⟨cur.rootId, cur.rootId_mem_nodeIds, 5, by decide, h⟩))
        (fun h => hno (Or.inl ⟨c.rootId, hc_in_cur, 3, by decide, h⟩))
        (fun h => hno (Or.inl ⟨c.rootId, hc_in_cur, 4, by decide, h⟩))
        (fun h => hno (Or.inl ⟨c.rootId, hc_in_cur, 5, by decide, h⟩))
      by_cases hnil : cur.items = []
      · exact Or.inl hnil
      · right
        rcases ItemListRep.tail_mem hnil hcur₁_mem.items_rep with ⟨it_l, hit_l, htl_eq, _⟩
        change s₁.mem (nodeBase + 12 * cur.rootId + 5) = it_l.id at htl_eq
        rw [htl_eq]
        exact fun h => hno (Or.inr ⟨it_l, hit_l, h⟩)
  have hfin := defillFinish_spec h16 hwf₂ hcur_ne_c hs2_c6 hs2_c7 hs2_nr
    (by rw [hfr_sp, hfr_pick]; exact hcur_root_lt) (by rw [hfr_sp]; exact hc_lt) hcur_fit
  rcases hfin with ⟨hv_fin, hfr_fin, hfin_cases⟩
  obtain ⟨s₃, hs₃_eq⟩ : ∃ s₃, s₃ = (Memory.spec 0).clientState s₂
      (defillFinish ![nodeBase, cur.rootId, c.rootId]) := ⟨_, rfl⟩
  rw [← hs₃_eq] at hfr_fin hfin_cases
  have hwf₃ : Memory.WellFormed w s₃ := by
    rw [hs₃_eq]; exact wellFormed_clientState hwf₂ hv_fin
  have hv_step : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (defillStep ![itemBase, nodeBase, cur.rootId])) := by
    dsimp only [defillStep]
    simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    refine validHistory_read_bind (by omega) (validHistory_read_bind (by omega)
      (validHistory_read_bind (by omega) (validHistory_read_bind (by omega) ?_)))
    have hcond_eq := eq_true hcond_mem
    simp only [hcond_eq, ↓reduceIte]
    refine validHistory_bind_step hv_pick ?_
    rw [hres_pick, hcur_sz, ← hs₁_eq]
    change (Memory.spec w).ValidHistory s₁ ((Memory.spec w).clientHistory s₁
      (defillSplice ![itemBase, nodeBase, cur.rootId, c.rootId, cur.items.length] >>=
        fun _ => defillFinish ![nodeBase, cur.rootId, c.rootId]))
    refine validHistory_bind_step hv_sp ?_
    rw [← hs₂_eq]
    exact hv_fin
  have hm_top : memoryCost (defillStep ![itemBase, nodeBase, cur.rootId]) s =
      4 + memoryCost (defillPickChild ![nodeBase, cur.rootId,
        s.mem (nodeBase + 12 * cur.rootId + 6),
        s.mem (nodeBase + 12 * cur.rootId + 7)]) s +
      memoryCost (defillSplice ![itemBase, nodeBase, cur.rootId, c.rootId, cur.items.length]) s₁ +
      memoryCost (defillFinish ![nodeBase, cur.rootId, c.rootId]) s₂ := by
    dsimp only [defillStep]
    simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    repeat (rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read])
    have hcond_eq := eq_true hcond_mem
    simp only [hcond_eq, ↓reduceIte]
    rw [memoryCost_bind', hres_pick, hcur_sz, ← hs₁_eq]
    change 1 + (1 + (1 + (1 + (memoryCost _ s +
      memoryCost (defillSplice _ >>= fun _ => defillFinish _) s₁)))) = _
    rw [memoryCost_bind', ← hs₂_eq]
    omega
  have hres_step : (Memory.spec 0).clientResult s
      (defillStep ![itemBase, nodeBase, cur.rootId]) =
      (Memory.spec 0).clientResult s₂ (defillFinish ![nodeBase, cur.rootId, c.rootId]) := by
    dsimp only [defillStep]
    simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    repeat rw [clientResult_bind_read]
    have hcond_eq := eq_true hcond_mem
    simp only [hcond_eq, ↓reduceIte]
    change (Memory.spec 0).clientResult s
      (defillPickChild ![nodeBase, cur.rootId, s.mem (nodeBase + 12 * cur.rootId + 6),
        s.mem (nodeBase + 12 * cur.rootId + 7)] >>= fun c =>
        defillSplice ![itemBase, nodeBase, cur.rootId, c, s.mem (nodeBase + 12 * cur.rootId + 3)]
          >>= fun _ => defillFinish ![nodeBase, cur.rootId, c]) = _
    rw [StateTransitionSpec.clientResult_bind, hres_pick, hcur_sz, ← hs₁_eq]
    rw [StateTransitionSpec.clientResult_bind, ← hs₂_eq]
  have hs_step : (Memory.spec 0).clientState s (defillStep ![itemBase, nodeBase, cur.rootId]) =
      s₃ := by
    dsimp only [defillStep]
    simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    repeat rw [clientState_bind_read]
    have hcond_eq := eq_true hcond_mem
    simp only [hcond_eq, ↓reduceIte]
    change (Memory.spec 0).clientState s
      (defillPickChild ![nodeBase, cur.rootId, s.mem (nodeBase + 12 * cur.rootId + 6),
        s.mem (nodeBase + 12 * cur.rootId + 7)] >>= fun c =>
        defillSplice ![itemBase, nodeBase, cur.rootId, c, s.mem (nodeBase + 12 * cur.rootId + 3)]
          >>= fun _ => defillFinish ![nodeBase, cur.rootId, c]) = s₃
    rw [StateTransitionSpec.clientState_bind, hres_pick, hcur_sz, ← hs₁_eq]
    rw [StateTransitionSpec.clientState_bind, ← hs₂_eq, ← hs₃_eq]
  have hm_sp_pos : 1 ≤ memoryCost
      (defillSplice ![itemBase, nodeBase, cur.rootId, c.rootId, cur.items.length]) s₁ := by
    dsimp only [defillSplice]
    rw [memoryCost_bind', memoryCost_read]
    omega
  have hcost_ge5 : 5 ≤ memoryCost (defillStep ![itemBase, nodeBase, cur.rootId]) s := by
    omega
  have hfin_cases' :
      if c.left.elim 0 SHTree.rootId = 0 ∧ c.right.elim 0 SHTree.rootId = 0 then
        memoryCost (defillStep ![itemBase, nodeBase, cur.rootId]) s ≤ 26 ∧
        (Memory.spec 0).clientResult s (defillStep ![itemBase, nodeBase, cur.rootId]) =
          cur.rootId ∧
        s₃.mem (nodeBase + 12 * cur.rootId + 6) = sib.elim 0 SHTree.rootId ∧
        s₃.mem (nodeBase + 12 * cur.rootId + 7) = 0 ∧
        ∀ a, a ≠ nodeBase + 12 * cur.rootId + 6 → a ≠ nodeBase + 12 * cur.rootId + 7 →
          s₃.mem a = s₂.mem a
      else
        memoryCost (defillStep ![itemBase, nodeBase, cur.rootId]) s ≤ 24 ∧
        (Memory.spec 0).clientResult s (defillStep ![itemBase, nodeBase, cur.rootId]) =
          c.rootId ∧
        s₃.mem (nodeBase + 12 * c.rootId + 8) = cur.rootId ∧
        ∀ a, a ≠ nodeBase + 12 * c.rootId + 8 → s₃.mem a = s₂.mem a := by
    by_cases hleaf : c.left.elim 0 SHTree.rootId = 0 ∧ c.right.elim 0 SHTree.rootId = 0
    · have hlc := eq_true hleaf
      simp only [hlc, ↓reduceIte] at hfin_cases ⊢
      rcases hfin_cases with ⟨hm_fin, hres_fin, h6, h7, hmem_f⟩
      exact ⟨by omega, hres_step.trans hres_fin, h6, h7, hmem_f⟩
    · have hlc := eq_false hleaf
      simp only [hlc, ↓reduceIte] at hfin_cases ⊢
      rcases hfin_cases with ⟨hm_fin, hres_fin, h8, hmem_f⟩
      exact ⟨by omega, hres_step.trans hres_fin, h8, hmem_f⟩
  have hcap_sum : (cur.items ++ c.items).length ≤ sizeCap rt cur.rank := by
    have h1 : 1 ≤ cur.rank := by rw [← hc_val.1]; omega
    have hrc : cur.rank = c.rank + 1 := hc_val.1.symm
    have hc_cap := hc_val.2.cap
    rw [hrc, sizeCap, List.length_append]
    have hlt : cur.items.length < targetSize rt (c.rank + 1) := by rw [← hrc]; exact hc_cond.1
    omega
  have hk8_cur' : cur.rank ≤ rt → ∀ it ∈ cur.items ++ c.items, it.origKey = c.ckey := by
    intro h8 it hit
    have hcur_nil : cur.items = [] := by
      have hts : targetSize rt cur.rank = 1 := targetSize_le_threshold h8
      have := hc_cond.1
      rw [hts] at this
      exact List.eq_nil_of_length_eq_zero (by omega)
    rw [hcur_nil, List.nil_append] at hit
    exact hc_val.2.rank_le_threshold (by omega) it hit
  have hle_cur' : ∀ it ∈ cur.items ++ c.items, it.origKey ≤ c.ckey := by
    intro it hit
    rcases List.mem_append.mp hit with h1 | h2
    · exact Nat.le_trans (hval.2.2.1 it h1) hc_val.2.lb_le
    · exact hc_val.2.origKey_le it h2
  have hcur_all_perm :
      (SHTree.node cur.rootId cur.rank cur.ckey cur.items (some c) sib).allItems.Perm
        cur.allItems ∧
      (∀ p ∈ (SHTree.node cur.rootId cur.rank cur.ckey cur.items (some c) sib).allEntries,
        p ∈ cur.allEntries) ∧
      (SHTree.node cur.rootId cur.rank cur.ckey cur.items (some c) sib).nodeIds.Perm
        cur.nodeIds ∧
      (∀ k, (SHTree.node cur.rootId cur.rank cur.ckey cur.items (some c) sib).countRank k =
        cur.countRank k) ∧
      (SHTree.node cur.rootId cur.rank cur.ckey cur.items (some c) sib).phi rt = cur.phi rt := by
    cases cur with
    | node id r ck items l r' =>
      dsimp only [SHTree.rootId, SHTree.rank, SHTree.ckey, SHTree.items,
        SHTree.left, SHTree.right] at hcsib ⊢
      rcases hcsib with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨.refl _, fun _ h => h, .refl _, fun _ => rfl, rfl⟩
      · refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · simp only [SHTree.allItems, SHTree.allEntries_node, List.map_append]
          rw [List.append_assoc, List.append_assoc]
          exact List.Perm.append_left _ List.perm_append_comm
        · intro p hp
          simp only [SHTree.allEntries_node, List.mem_append, Option.elim_some] at hp ⊢
          rcases hp with (h1 | h2) | h3
          · exact Or.inl (Or.inl h1)
          · exact Or.inr h2
          · exact Or.inl (Or.inr h3)
        · simp only [SHTree.nodeIds_node, List.cons_append, Option.elim_some]
          exact List.Perm.cons _ List.perm_append_comm
        · intro k; simp only [SHTree.countRank_node, Option.elim_some]; omega
        · simp only [SHTree.phi, SHTree.itemPhiSum_node, SHTree.nodeCount_node, Option.elim_some]
          push_cast; ring
  have hsib_sub_node : ∀ nid ∈ sib.elim [] SHTree.nodeIds,
      nid ≠ cur.rootId ∧ nid ≠ c.rootId ∧ nid ∈ cur.nodeIds := by
    intro nid hnid
    have hnd_swap : (SHTree.node cur.rootId cur.rank cur.ckey cur.items
        (some c) sib).nodeIds.Nodup :=
      hcur_all_perm.2.2.1.nodup_iff.mpr hcur_nd
    have hnd_swap' : cur.rootId ∉ c.nodeIds ++ sib.elim [] SHTree.nodeIds ∧
        (c.nodeIds ++ sib.elim [] SHTree.nodeIds).Nodup := by
      rw [← List.nodup_cons]
      simpa only [SHTree.nodeIds_node, Option.elim_some, List.cons_append] using hnd_swap
    have hn_cur : nid ≠ cur.rootId :=
      fun heq => hnd_swap'.1 (List.mem_append_right _ (heq ▸ hnid))
    have hn_c : nid ≠ c.rootId := fun heq =>
      (list_nodup_append_disj hnd_swap'.2).2.2 nid (heq ▸ c.rootId_mem_nodeIds) hnid
    have hn_in : nid ∈ cur.nodeIds := by
      apply hcur_all_perm.2.2.1.mem_iff.mp
      simp [SHTree.nodeIds_node, hnid]
    exact ⟨hn_cur, hn_c, hn_in⟩
  have hsib_sub_item : ∀ it ∈ sib.elim [] SHTree.allItems,
      it ∉ cur.items ∧ it ∉ c.items ∧ it ∈ cur.allItems := by
    intro it hit
    have hid_swap : (SHTree.node cur.rootId cur.rank cur.ckey cur.items
        (some c) sib).itemIds.Nodup := by
      have hp : (SHTree.node cur.rootId cur.rank cur.ckey cur.items (some c) sib).itemIds.Perm
          cur.itemIds := hcur_all_perm.1.map SHItem.id
      exact hp.nodup_iff.mpr hcur_item_nd
    rw [SHTree.itemIds_node, Option.elim_some] at hid_swap
    have h1 := list_nodup_append_disj hid_swap
    have hit_id : it.id ∈ sib.elim [] SHTree.itemIds := by
      cases sib with
      | none => cases hit
      | some st => exact List.mem_map_of_mem hit
    have hn1' : it ∉ cur.items := fun hx =>
      h1.2.2 it.id (List.mem_append_left _ (List.mem_map_of_mem hx)) hit_id
    have hn2 : it ∉ c.items := fun hx => by
      have hx_c : it.id ∈ c.itemIds := by
        cases c
        dsimp only [SHTree.items] at hx
        rw [SHTree.itemIds_node]
        exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hx))
      exact h1.2.2 it.id (List.mem_append_right _ hx_c) hit_id
    have hin : it ∈ cur.allItems := hcur_all_perm.1.mem_iff.mp (by
      rw [SHTree.allItems_node, Option.elim_some]
      exact List.mem_append_right _ hit)
    exact ⟨hn1', hn2, hin⟩
  have hs2_not_sib : ∀ nid ∈ sib.elim [] SHTree.nodeIds, ∀ j < 12,
      s₂.mem (nodeBase + 12 * nid + j) = s.mem (nodeBase + 12 * nid + j) := by
    intro nid hnid j hj
    have hn := hsib_sub_node nid hnid
    have hs1_eq : s₁.mem (nodeBase + 12 * nid + j) = s.mem (nodeBase + 12 * nid + j) :=
      hmem_pick _ (by omega) (by omega)
    rw [← hs1_eq]
    apply hmem_sp _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    by_cases hnil : cur.items = []
    · exact Or.inl hnil
    · right
      rcases ItemListRep.tail_mem hnil hcur₁_mem.items_rep with ⟨it_l, hit_l, htl_eq, _⟩
      change s₁.mem (nodeBase + 12 * cur.rootId + 5) = it_l.id at htl_eq
      rw [htl_eq]
      exact hdisj nid (hcur_sub nid hn.2.2) it_l
        (hcur_items_sub it_l (by
          cases cur; dsimp only [SHTree.items] at hit_l; simp [SHTree.allItems_node, hit_l]))
        j hj 2 (by decide)
  have hs2_not_sib_item : ∀ it ∈ sib.elim [] SHTree.allItems, ∀ j < 3,
      s₂.mem (itemBase + 3 * it.id + j) = s.mem (itemBase + 3 * it.id + j) := by
    intro it hit j hj
    have hi := hsib_sub_item it hit
    have hi_in := hcur_items_sub it hi.2.2
    have hs1_eq : s₁.mem (itemBase + 3 * it.id + j) = s.mem (itemBase + 3 * it.id + j) := by
      refine hmem_pick _ ?_ ?_
      · exact (hdisj cur.rootId (hcur_sub cur.rootId cur.rootId_mem_nodeIds) it hi_in
          6 (by decide) j hj).symm
      · exact (hdisj cur.rootId (hcur_sub cur.rootId cur.rootId_mem_nodeIds) it hi_in
          7 (by decide) j hj).symm
    rw [← hs1_eq]
    apply hmem_sp _
      (hdisj cur.rootId (hcur_sub _ cur.rootId_mem_nodeIds) it hi_in 0 (by decide) j hj).symm
      (hdisj cur.rootId (hcur_sub _ cur.rootId_mem_nodeIds) it hi_in 3 (by decide) j hj).symm
      (hdisj cur.rootId (hcur_sub _ cur.rootId_mem_nodeIds) it hi_in 4 (by decide) j hj).symm
      (hdisj cur.rootId (hcur_sub _ cur.rootId_mem_nodeIds) it hi_in 5 (by decide) j hj).symm
      (hdisj c.rootId (hcur_sub c.rootId hc_in_cur) it hi_in 3 (by decide) j hj).symm
      (hdisj c.rootId (hcur_sub c.rootId hc_in_cur) it hi_in 4 (by decide) j hj).symm
      (hdisj c.rootId (hcur_sub c.rootId hc_in_cur) it hi_in 5 (by decide) j hj).symm
    by_cases hnil : cur.items = []
    · exact Or.inl hnil
    · right
      rcases ItemListRep.tail_mem hnil hcur₁_mem.items_rep with ⟨it_l, hit_l, htl_eq, _⟩
      change s₁.mem (nodeBase + 12 * cur.rootId + 5) = it_l.id at htl_eq
      rw [htl_eq]
      have hne_id : it.id ≠ it_l.id := by
        intro heq
        have hid_eq : cur.itemIds = cur.items.map SHItem.id ++
            (cur.left.elim [] SHTree.itemIds ++ cur.right.elim [] SHTree.itemIds) := by
          cases cur
          simp [SHTree.itemIds_node, SHTree.items, SHTree.left, SHTree.right, List.append_assoc]
        have hdisj_it := (list_nodup_append_disj
          (by rw [hid_eq] at hcur_item_nd; exact hcur_item_nd)).2.2
        have hit_sib : it.id ∈ sib.elim [] SHTree.itemIds := by
          cases sib with
          | none => cases hit
          | some st => exact List.mem_map_of_mem hit
        apply hdisj_it it_l.id (List.mem_map_of_mem hit_l)
        rw [← heq]
        cases cur with
        | node id r ck items l r' =>
          dsimp only [SHTree.left, SHTree.right] at hcsib ⊢
          rcases hcsib with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact List.mem_append_right _ hit_sib
          · exact List.mem_append_left _ hit_sib
      omega
  exact ⟨c, sib, s₁, s₂, s₃, ⟨hfr_pick, hmem_pick, hcsib, hc_le_sib, hcur_ne_c, hc_val, hc_mem,
    hcur₁_mem, hv_sp, hm_sp, hfr_sp, hmem_sp, hs2_0, hs2_3, hs2_45, hs2_c3, hs2_c4, hs2_c5, hwf₃,
    hfr_fin, hfin_cases', hv_step, hcost_ge5, hcap_sum, hk8_cur', hle_cur', hcur_all_perm,
    hsib_sub_node, hsib_sub_item, hs2_not_sib, hs2_not_sib_item, hs_step, hc_in_cur,
    hs2_frame⟩⟩

private theorem defill_zipFrames_step {rt itemBase nodeBase : ℕ} {t₀ cur cur' : SHTree}
    {ctx : List ZipFrame} {mem₁ mem₂ : ℕ → ℕ} {lb : ℕ}
    (hcur_sub : ∀ id ∈ cur.nodeIds, id ∈ t₀.nodeIds)
    (hcur_items_sub : ∀ it ∈ cur.allItems, it ∈ t₀.allItems)
    (hnd : (zipRebuild cur ctx).nodeIds.Nodup)
    (hsub : ∀ id ∈ (zipRebuild cur ctx).nodeIds, id ∈ t₀.nodeIds)
    (hid_nd : (zipRebuild cur ctx).itemIds.Nodup)
    (hperm : (zipRebuild cur ctx).allItems.Perm t₀.allItems)
    (hdisj : ∀ id ∈ t₀.nodeIds, ∀ it ∈ t₀.allItems, ∀ j < 12, ∀ k < 3,
      nodeBase + 12 * id + j ≠ itemBase + 3 * it.id + k)
    (hframe' : ∀ a, mem₂ a ≠ mem₁ a →
      (∃ id ∈ cur.nodeIds, ∃ j < 9, a = nodeBase + 12 * id + j) ∨
      (∃ it ∈ cur.items, a = itemBase + 3 * it.id + 2))
    (h8 : mem₁ (nodeBase + 12 * cur.rootId + 8) = mem₂ (nodeBase + 12 * cur'.rootId + 8))
    (hid : cur.rootId = cur'.rootId) (hrk : cur.rank = cur'.rank)
    (hframes : ZipFramesRep rt itemBase nodeBase mem₁ cur ctx lb) :
    ZipFramesRep rt itemBase nodeBase mem₂ cur' ctx lb := by
  refine ZipFramesRep_replace_cur hid hrk h8 ?_ ?_ hframes
  · intro id hid_ctx j hj
    by_contra hneq
    rcases hframe' _ (Ne.symm hneq) with ⟨id', hid', j', hj', ha⟩ | ⟨it, hit, ha⟩
    · have : id = id' := by omega
      subst this
      have hp := (zipRebuild_nodeIds_perm cur ctx).nodup_iff.mp hnd
      exact (List.nodup_append.mp hp).2.2 _ hid' _ hid_ctx rfl
    · exact (hdisj id (hsub id ((zipRebuild_nodeIds_perm cur ctx).mem_iff.mpr
        (List.mem_append_right _ hid_ctx)))
        it (hcur_items_sub it (by
          cases cur; dsimp only [SHTree.items] at hit; simp [SHTree.allItems_node, hit]))
        j (by omega) 2 (by decide)) ha
  · intro it hit_ctx j hj
    by_contra hneq
    rcases hframe' _ (Ne.symm hneq) with ⟨id', hid', j', hj', ha⟩ | ⟨it', hit', ha⟩
    · have hit_t₀ : it ∈ t₀.allItems := by
        have hperm_ctx : ∀ g ∈ ctx, ∀ x ∈ g.items ++ g.sibling.elim [] SHTree.allItems,
            x ∈ t₀.allItems := by
          intro g hg x hx
          apply hperm.mem_iff.mp
          apply ((zipRebuild_allEntries_perm cur ctx).map Prod.fst).mem_iff.mpr
          rw [List.map_append]
          apply List.mem_append_right
          simp only [List.mem_map, List.mem_flatMap]
          rcases List.mem_append.mp hx with hx1 | hx2
          · exact ⟨(x, g.ckey), ⟨g, hg,
              List.mem_append_left _ (List.mem_map.mpr ⟨x, hx1, rfl⟩)⟩, rfl⟩
          · cases hs : g.sibling with
            | none => simp [hs] at hx2
            | some sb =>
              simp only [hs, Option.elim_some, SHTree.allItems, List.mem_map] at hx2
              rcases hx2 with ⟨p, hp, rfl⟩
              exact ⟨p, ⟨g, hg, List.mem_append_right _ (by simp [hs, hp])⟩, rfl⟩
        simp only [List.mem_flatMap] at hit_ctx
        rcases hit_ctx with ⟨g, hg, hmem_g⟩
        exact hperm_ctx g hg it hmem_g
      exact (hdisj id' (hcur_sub id' hid') it hit_t₀ j' (by omega) j hj) ha.symm
    · have : it.id = it'.id := by omega
      have hit_in_cur : it'.id ∈ List.map (SHItem.id ∘ Prod.fst) cur.allEntries := by
        rw [List.mem_map]
        refine ⟨(it', cur.ckey), ?_, rfl⟩
        cases cur
        dsimp only [SHTree.items, SHTree.ckey] at hit' ⊢
        simp [SHTree.allEntries_node, hit']
      have hit_in_ctx : it.id ∈ (ctx.flatMap (fun g => g.items.map (fun x => (x, g.ckey)) ++
          g.sibling.elim [] SHTree.allEntries)).map (SHItem.id ∘ Prod.fst) := by
        simp only [List.mem_map, List.mem_flatMap] at hit_ctx ⊢
        rcases hit_ctx with ⟨g, hg, hmem_g⟩
        rcases List.mem_append.mp hmem_g with h1 | h2
        · exact ⟨(it, g.ckey), ⟨g, hg,
            List.mem_append_left _ (List.mem_map.mpr ⟨it, h1, rfl⟩)⟩, rfl⟩
        · cases hs : g.sibling with
          | none => simp [hs] at h2
          | some sb =>
            simp only [hs, Option.elim_some, SHTree.allItems, List.mem_map] at h2
            rcases h2 with ⟨p, hp, rfl⟩
            exact ⟨p, ⟨g, hg, List.mem_append_right _ (by simp [hs, hp])⟩, rfl⟩
      have hnd_item := ((zipRebuild_allEntries_perm cur ctx).map Prod.fst).map SHItem.id
        |>.nodup_iff.mp hid_nd
      rw [List.map_append, List.map_append, List.map_map, List.map_map,
        List.nodup_append] at hnd_item
      exact hnd_item.2.2 it'.id hit_in_cur it.id hit_in_ctx this.symm

private theorem defillStep_leaf_spec {rt w itemBase nodeBase : ℕ} {t₀ cur c : SHTree}
    {sib : Option SHTree} {ctx : List ZipFrame} {s s₁ s₂ s₃ : Memory.State}
    (hinv : ZipInv rt w itemBase nodeBase t₀ (some cur) ctx s)
    (hinfo : DefillCurInfo rt itemBase nodeBase t₀ cur s)
    (hps : DefillStepPSRes rt w itemBase nodeBase t₀ cur c sib s s₁ s₂ s₃)
    (hleaf : c.left.elim 0 SHTree.rootId = 0 ∧ c.right.elim 0 SHTree.rootId = 0) :
    DefillStepPost rt w itemBase nodeBase t₀ cur ctx s := by
  rcases hinv with ⟨h16, hmem, hn_lt, hi_lt, hdisj, hrootId, hrank, hnd, hsub, hdead, hid_nd,
    hcrk, hperm, hck_mono, hroot_ck, hcur_mem, lb, hval, hframes⟩
  rcases hinfo with ⟨hcur_sub, hcur_nd, hcur_items_sub, hcur_item_nd, hcur_root_lt,
    hcur_sz, hcur_tgt, hcur_l, hcur_r, hcur_l0_iff, hcur_r0_iff⟩
  rcases hps with ⟨hfr_pick, hmem_pick, hcsib, hc_le_sib, hcur_ne_c, hc_val, hc_mem, hcur₁_mem,
    _, _, hfr_sp, hmem_sp, hs2_0, hs2_3, hs2_45, hs2_c3, hs2_c4, hs2_c5, hwf₃, hfr_fin,
    hfin_cases, hv_step, hcost_ge5, hcap_sum, hk8_cur', hle_cur', hcur_all_perm, hsib_sub_node,
    hsib_sub_item, hs2_not_sib, hs2_not_sib_item, hs_step, hc_in_cur, hs2_frame⟩
  have hc_lr_none : c.left = none ∧ c.right = none := by
    cases hcl : c.left with
    | none =>
      cases hcr : c.right with
      | none => exact ⟨rfl, rfl⟩
      | some cr =>
        have hne : cr.rootId ≠ 0 := (hc_mem.right_mem cr hcr).rootId_ne
        simp [hcl, hcr, hne] at hleaf
    | some cl =>
      have hne : cl.rootId ≠ 0 := (hc_mem.left_mem cl hcl).rootId_ne
      simp [hcl, hne] at hleaf
  have hlc := eq_true hleaf
  simp only [hlc, ↓reduceIte] at hfin_cases
  rcases hfin_cases with ⟨hm_step_le, hres_step, h3_6, h3_7, hmem_fin⟩
  let cur' : SHTree := .node cur.rootId cur.rank c.ckey (cur.items ++ c.items) sib none
  have hframe_mem' : ∀ a, s₃.mem a ≠ s.mem a →
      (∃ id ∈ cur.nodeIds, ∃ j < 8, a = nodeBase + 12 * id + j) ∨
      (∃ it ∈ cur.items, a = itemBase + 3 * it.id + 2) := by
    intro a ha
    by_cases hfin_eq : s₃.mem a = s₂.mem a
    · rw [hfin_eq] at ha; exact hs2_frame a ha
    · by_contra hno
      exact hfin_eq (hmem_fin a
        (fun h => hno (Or.inl ⟨cur.rootId, cur.rootId_mem_nodeIds, 6, by decide, h⟩))
        (fun h => hno (Or.inl ⟨cur.rootId, cur.rootId_mem_nodeIds, 7, by decide, h⟩)))
  have hframe_mem : ∀ a, s₃.mem a ≠ s.mem a →
      (∃ id ∈ t₀.nodeIds, ∃ j < 9, a = nodeBase + 12 * id + j) ∨
      (∃ it ∈ t₀.allItems, a = itemBase + 3 * it.id + 2) := by
    intro a ha
    rcases hframe_mem' a ha with ⟨id, hid, j, hj, ha'⟩ | ⟨it, hit, ha'⟩
    · exact Or.inl ⟨id, hcur_sub id hid, j, by omega, ha'⟩
    · exact Or.inr ⟨it, hcur_items_sub it (by
        cases cur; dsimp only [SHTree.items] at hit; simp [SHTree.allItems_node, hit]), ha'⟩
  have hsib_mem3 : ∀ sc, sib = some sc → TreeMemRep rt itemBase nodeBase s₃.mem sc := by
    intro sc hsc
    have hsib_s : TreeMemRep rt itemBase nodeBase s.mem sc := by
      rcases hcsib with ⟨_, hr⟩ | ⟨_, hl⟩
      · exact hcur_mem.right_mem sc (hr.symm ▸ hsc)
      · exact hcur_mem.left_mem sc (hl.symm ▸ hsc)
    refine TreeMemRep.congr (fun nid hnid j hj => ?_) (fun it hit j hj => ?_) hsib_s
    · have hne_cur : nid ≠ cur.rootId :=
        (hsib_sub_node nid (by simp [hsc, hnid])).1
      have hs3_eq := hmem_fin (nodeBase + 12 * nid + j) (by omega) (by omega)
      exact (hs2_not_sib nid (by simp [hsc, hnid]) j (by omega)).symm.trans hs3_eq.symm
    · have hit_sib : it ∈ sib.elim [] SHTree.allItems := by simp [hsc, hit]
      have hi_in := (hsib_sub_item it hit_sib).2.2
      have hd := hdisj cur.rootId (hcur_sub _ cur.rootId_mem_nodeIds) it
        (hcur_items_sub it hi_in)
      have hs3_eq := hmem_fin (itemBase + 3 * it.id + j)
        (hd 6 (by decide) j hj).symm (hd 7 (by decide) j hj).symm
      exact (hs2_not_sib_item it hit_sib j hj).symm.trans hs3_eq.symm
  have hcur'_nd : cur'.nodeIds.Nodup := by
    have hnd_sw := hcur_all_perm.2.2.1.nodup_iff.mpr hcur_nd
    rw [SHTree.nodeIds_node, Option.elim_some, List.cons_append, List.nodup_cons] at hnd_sw
    simp only [cur', SHTree.nodeIds_node, Option.elim_none, List.append_nil, List.nodup_cons]
    exact ⟨fun h => hnd_sw.1 (List.mem_append_right _ h), (List.nodup_append.mp hnd_sw.2).2.1⟩
  have hc_leaf_ids : c.nodeIds = [c.rootId] := by
    cases c
    dsimp only [SHTree.left, SHTree.right] at hc_lr_none
    simp [SHTree.nodeIds_node, SHTree.rootId, hc_lr_none.1, hc_lr_none.2]
  let framesN := ctx.flatMap (fun f => f.id :: f.sibling.elim [] SHTree.nodeIds)
  have hcur_ctx_perm : (cur.nodeIds ++ framesN).Perm
      (c.rootId :: (cur'.nodeIds ++ framesN)) := by
    have hp1 : cur.nodeIds.Perm (c.rootId :: cur'.nodeIds) := by
      refine hcur_all_perm.2.2.1.symm.trans ?_
      simp only [cur', SHTree.nodeIds_node, Option.elim_some, Option.elim_none, List.append_nil,
        hc_leaf_ids, List.cons_append, List.nil_append]
      exact List.Perm.swap _ _ _
    exact List.Perm.append_right framesN hp1
  have hnd_c_whole : (c.rootId :: (cur'.nodeIds ++ framesN)).Nodup :=
    ((zipRebuild_nodeIds_perm cur ctx).trans hcur_ctx_perm).nodup_iff.mp hnd
  have hwhole'_nd : (zipRebuild cur' ctx).nodeIds.Nodup :=
    (zipRebuild_nodeIds_perm cur' ctx).nodup_iff.mpr (List.nodup_cons.mp hnd_c_whole).2
  have hwhole'_sub : ∀ id ∈ (zipRebuild cur' ctx).nodeIds, id ∈ t₀.nodeIds := by
    intro id hid
    apply hsub id
    exact (zipRebuild_nodeIds_perm cur ctx).mem_iff.mpr (hcur_ctx_perm.mem_iff.mpr
      (List.mem_cons_of_mem _ ((zipRebuild_nodeIds_perm cur' ctx).mem_iff.mp hid)))
  have hc4_s3 : s₃.mem (nodeBase + 12 * c.rootId + 4) = 0 := by
    have hs3_eq := hmem_fin (nodeBase + 12 * c.rootId + 4) (by omega) (by omega)
    exact hs3_eq.trans hs2_c4
  have hdead' : ∀ id ∈ t₀.nodeIds, id ∉ (zipRebuild cur' ctx).nodeIds →
      s₃.mem (nodeBase + 12 * id + 4) = 0 := by
    intro id hid hnotin
    by_cases heq_c : id = c.rootId
    · subst heq_c; exact hc4_s3
    · have hnot_old : id ∉ (zipRebuild cur ctx).nodeIds := by
        intro hin
        have hm := hcur_ctx_perm.mem_iff.mp ((zipRebuild_nodeIds_perm cur ctx).mem_iff.mp hin)
        rcases List.mem_cons.mp hm with heqc | hmem'
        · exact heq_c heqc
        · exact hnotin ((zipRebuild_nodeIds_perm cur' ctx).mem_iff.mpr hmem')
      have heq_s : s₃.mem (nodeBase + 12 * id + 4) = s.mem (nodeBase + 12 * id + 4) := by
        by_contra hneq
        rcases hframe_mem' _ hneq with ⟨id', hid', _, _, ha⟩ | ⟨it, hit, ha⟩
        · have : id = id' := by omega
          subst this
          exact hnot_old (zipRebuild_nodeIds_sub cur ctx _ hid')
        · exact (hdisj id hid it (hcur_items_sub it (by
            cases cur; dsimp only [SHTree.items] at hit; simp [SHTree.allItems_node, hit]))
            4 (by decide) 2 (by decide)) ha
      exact heq_s.trans (hdead id hid hnot_old)
  have hcur'_mem3 : TreeMemRep rt itemBase nodeBase s₃.mem cur' := by
    have hs3_cur : ∀ off, off = 1 ∨ off = 2 →
        s₃.mem (nodeBase + 12 * cur.rootId + off) = s.mem (nodeBase + 12 * cur.rootId + off) := by
      intro off hoff
      have hs2 : s₂.mem (nodeBase + 12 * cur.rootId + off) =
          s₁.mem (nodeBase + 12 * cur.rootId + off) := by
        apply hmem_sp _ (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega)
        by_cases hnil : cur.items = []
        · exact Or.inl hnil
        · right
          rcases ItemListRep.tail_mem hnil hcur₁_mem.items_rep with ⟨it_l, hit_l, htl_eq, _⟩
          change s₁.mem (nodeBase + 12 * cur.rootId + 5) = it_l.id at htl_eq
          rw [htl_eq]
          have hit_cur : it_l ∈ cur.allItems := by
            cases cur; dsimp only [SHTree.items] at hit_l; simp [SHTree.allItems_node, hit_l]
          rcases hoff with rfl | rfl <;>
            exact hdisj cur.rootId (hcur_sub _ cur.rootId_mem_nodeIds) it_l
              (hcur_items_sub it_l hit_cur) _ (by decide) 2 (by decide)
      exact (hmem_fin _ (by omega) (by omega)).trans
        (hs2.trans (hmem_pick _ (by omega) (by omega)))
    have h12 : s₃.mem (nodeBase + 12 * cur.rootId + 1) = cur.rank :=
      (hs3_cur 1 (Or.inl rfl)).trans hcur_mem.rank_eq
    have h22 : s₃.mem (nodeBase + 12 * cur.rootId + 2) = targetSize rt cur.rank :=
      (hs3_cur 2 (Or.inr rfl)).trans hcur_mem.target_eq
    have hlist3 : ItemListRep itemBase s₃.mem (s₃.mem (nodeBase + 12 * cur.rootId + 4))
        (s₃.mem (nodeBase + 12 * cur.rootId + 5)) (cur.items ++ c.items) := by
      rw [hmem_fin _ (by omega) (by omega), hmem_fin _ (by omega) (by omega)]
      refine ItemListRep.congr (fun it hit j hj => ?_) hs2_45
      have hit' : it ∈ cur.allItems := by
        rcases List.mem_append.mp hit with h1 | h2
        · cases cur; dsimp only [SHTree.items] at h1; simp [SHTree.allItems_node, h1]
        · have h2c : it ∈ c.allItems := by
            cases c; dsimp only [SHTree.items] at h2; simp [SHTree.allItems_node, h2]
          cases cur with | node _ _ _ _ _ _ =>
          rcases hcsib with ⟨hl, _⟩ | ⟨hr, _⟩
          · dsimp only [SHTree.left] at hl; simp [SHTree.allItems_node, hl, h2c]
          · dsimp only [SHTree.right] at hr; simp [SHTree.allItems_node, hr, h2c]
      have hd := hdisj cur.rootId (hcur_sub _ cur.rootId_mem_nodeIds) it
        (hcur_items_sub it hit')
      exact (hmem_fin _ (hd 6 (by decide) j hj).symm (hd 7 (by decide) j hj).symm).symm
    exact .node hcur_mem.rootId_ne
      ((hmem_fin _ (by omega) (by omega)).trans hs2_0) h12 h22
      ((hmem_fin _ (by omega) (by omega)).trans hs2_3) hlist3 h3_6 h3_7
      hsib_mem3 (fun _ h => by cases h)
  have hcur'_all_perm : cur'.allItems.Perm cur.allItems := by
    refine List.Perm.trans ?_ hcur_all_perm.1
    have hc_eq : c.allItems = c.items := by
      cases c
      dsimp only [SHTree.left, SHTree.right] at hc_lr_none
      simp [SHTree.allItems_node, SHTree.items, hc_lr_none.1, hc_lr_none.2]
    simp only [cur', SHTree.allItems_node, Option.elim_some, Option.elim_none,
      List.append_nil, hc_eq, List.append_assoc]
    exact .refl _
  have hwhole'_all_perm : (zipRebuild cur' ctx).allItems.Perm t₀.allItems := by
    refine (((zipRebuild_allEntries_perm cur' ctx).map Prod.fst).trans ?_).trans
      ((zipRebuild_allEntries_perm cur ctx).map Prod.fst).symm |>.trans hperm
    simp only [List.map_append]
    exact List.Perm.append_right _ hcur'_all_perm
  have hwhole'_item_nd : (zipRebuild cur' ctx).itemIds.Nodup := by
    have hp := (hwhole'_all_perm.trans hperm.symm).map SHItem.id
    exact hp.nodup_iff.mpr hid_nd
  have hwhole'_ck_mono : ∀ p ∈ (zipRebuild cur' ctx).allEntries,
      ∃ c₀, (p.1, c₀) ∈ t₀.allEntries ∧ c₀ ≤ p.2 := by
    intro p hp
    have hp' := (zipRebuild_allEntries_perm cur' ctx).mem_iff.mp hp
    rcases List.mem_append.mp hp' with hp_cur' | hp_ctx
    · simp only [cur', SHTree.allEntries_node, Option.elim_none, List.append_nil,
        List.mem_append, List.mem_map] at hp_cur'
      rcases hp_cur' with ⟨it, hit, rfl⟩ | hsib_e
      · rcases hit with h1 | h2
        · have hin : (it, cur.ckey) ∈ (zipRebuild cur ctx).allEntries :=
            (zipRebuild_allEntries_perm cur ctx).mem_iff.mpr (List.mem_append_left _ (by
              cases cur; dsimp only [SHTree.items, SHTree.ckey] at h1 ⊢
              simp [SHTree.allEntries_node, h1]))
          rcases hck_mono _ hin with ⟨c₀, hc₀, hle₀⟩
          exact ⟨c₀, hc₀, Nat.le_trans hle₀ hc_val.2.lb_le⟩
        · have hc_ent : c.allEntries = c.items.map (fun it => (it, c.ckey)) := by
            cases c
            dsimp only [SHTree.left, SHTree.right] at hc_lr_none
            simp [SHTree.allEntries_node, SHTree.items, SHTree.ckey, hc_lr_none.1, hc_lr_none.2]
          have hin_c : (it, c.ckey) ∈ cur.allEntries := hcur_all_perm.2.1 _ (by
            simp [SHTree.allEntries_node, hc_ent, h2])
          have hin : (it, c.ckey) ∈ (zipRebuild cur ctx).allEntries :=
            (zipRebuild_allEntries_perm cur ctx).mem_iff.mpr (List.mem_append_left _ hin_c)
          exact hck_mono _ hin
      · have hin_s : p ∈ cur.allEntries := hcur_all_perm.2.1 _ (by
          simp only [SHTree.allEntries_node, List.mem_append]; exact Or.inr hsib_e)
        exact hck_mono _ ((zipRebuild_allEntries_perm cur ctx).mem_iff.mpr
          (List.mem_append_left _ hin_s))
    · exact hck_mono _ ((zipRebuild_allEntries_perm cur ctx).mem_iff.mpr
        (List.mem_append_right _ hp_ctx))
  have hwhole'_crk : ∀ k, (zipRebuild cur' ctx).countRank k ≤ t₀.countRank k := by
    intro k
    have hcrk_k := hcrk k
    rw [zipRebuild_countRank] at hcrk_k
    rw [zipRebuild_countRank]
    refine Nat.le_trans ?_ hcrk_k
    have hc'_le : cur'.countRank k ≤ cur.countRank k := by
      rw [← hcur_all_perm.2.2.2.1 k]
      simp [cur', SHTree.countRank_node]
    omega
  have hcur'_val : ZipCurValid rt lb cur' := by
    refine ⟨hcap_sum, Nat.le_trans hval.2.1 hc_val.2.lb_le, hle_cur', hk8_cur',
      fun hnil => ?_, fun sc hsc => ?_, fun _ h => by cases h⟩
    · dsimp only [cur', SHTree.items] at hnil
      exact absurd (List.append_eq_nil_iff.mp hnil).2 hc_val.2.items_ne
    · rcases hcsib with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · have h2 := hval.2.2.2.2.2.2 sc hsc
        exact ⟨h2.1, h2.2.replace_lb (hc_le_sib sc hsc)⟩
      · have h1 := hval.2.2.2.2.2.1 sc hsc
        exact ⟨h1.1, h1.2.replace_lb (hc_le_sib sc hsc)⟩
  have hcur_8 : s.mem (nodeBase + 12 * cur.rootId + 8) =
      s₃.mem (nodeBase + 12 * cur'.rootId + 8) := by
    by_contra hneq
    rcases hframe_mem' _ (Ne.symm hneq) with ⟨id', _, j, hj, ha⟩ | ⟨it, hit, ha⟩
    · dsimp only [cur', SHTree.rootId] at ha; omega
    · exact (hdisj cur.rootId (hcur_sub _ cur.rootId_mem_nodeIds) it
        (hcur_items_sub it (by
          cases cur; dsimp only [SHTree.items] at hit; simp [SHTree.allItems_node, hit]))
        8 (by decide) 2 (by decide)) ha
  have hframes' : ZipFramesRep rt itemBase nodeBase s₃.mem cur' ctx lb :=
    defill_zipFrames_step hcur_sub hcur_items_sub hnd hsub hid_nd hperm hdisj
      (fun a ha => by
        rcases hframe_mem' a ha with ⟨id, hid, j, hj, ha'⟩ | h
        · exact Or.inl ⟨id, hid, j, by omega, ha'⟩
        · exact Or.inr h)
      hcur_8 rfl rfl hframes
  have hwhole'_rootId : (zipRebuild cur' ctx).rootId = t₀.rootId := by
    rw [zipRebuild_rootId]
    change ctx.getLast?.elim cur.rootId ZipFrame.id = t₀.rootId
    rw [← zipRebuild_rootId]
    exact hrootId
  have hwhole'_rank : (zipRebuild cur' ctx).rank = t₀.rank := by
    cases ctx with
    | nil => simpa [zipRebuild, cur', SHTree.rank] using hrank
    | cons f rest =>
      have := (zipRebuild_rank cur (f :: rest)).2 f rest rfl
      have := (zipRebuild_rank cur' (f :: rest)).2 f rest rfl
      omega
  have hwhole'_ck : t₀.items ≠ [] → t₀.ckey ≤ (zipRebuild cur' ctx).ckey := by
    intro hne
    cases ctx with
    | nil =>
      simp only [zipRebuild] at hroot_ck ⊢
      exact Nat.le_trans (hroot_ck hne) hc_val.2.lb_le
    | cons g rest =>
      simp only [zipRebuild] at hroot_ck ⊢
      rw [zipRebuild_ckey_of_cons cur' cur g rest]
      exact hroot_ck hne
  have hphi_drop : cur'.phi rt + 30 ≤ cur.phi rt := by
    rw [← hcur_all_perm.2.2.2.2]
    dsimp only [SHTree.left, SHTree.right] at hc_lr_none
    have hc_phi : c.itemPhiSum rt = (c.items.length : ℚ) * itemPhi rt c.rank := by
      cases c; simp [SHTree.itemPhiSum_node, SHTree.items, SHTree.rank, hc_lr_none.1, hc_lr_none.2]
    have hc_nc : c.nodeCount = 1 := by
      cases c; simp [SHTree.nodeCount_node, hc_lr_none.1, hc_lr_none.2]
    have hsub_itemPhi := itemPhi_sub_succ rt c.rank
    have hc_rank1 : cur.rank = c.rank + 1 := hc_val.1.symm
    simp only [cur', SHTree.phi, SHTree.itemPhiSum_node, SHTree.nodeCount_node, hc_phi, hc_nc,
      Option.elim_some, Option.elim_none, add_zero, hc_rank1, List.length_append]
    have hpos_ts : (0 : ℚ) < (targetSize rt c.rank : ℚ) := by
      exact_mod_cast targetSize_pos rt c.rank
    have hdrop_pos :
        (0 : ℚ) ≤ (c.items.length : ℚ) * (itemPhi rt c.rank - itemPhi rt (c.rank + 1)) := by
      rw [hsub_itemPhi]
      exact mul_nonneg (Nat.cast_nonneg _) (div_nonneg zero_le_one hpos_ts.le)
    push_cast
    linarith
  unfold DefillStepPost
  refine ⟨hv_step, some cur', ctx, ?_, ?_, ?_, hcost_ge5, ?_⟩
  · dsimp only [cur', SHTree.rootId]; exact hres_step
  · rw [hs_step]; exact hfr_fin.trans (hfr_sp.trans hfr_pick)
  · rw [hs_step]; exact hframe_mem
  · rw [hs_step]
    refine ⟨⟨h16, hwf₃,
      fun id hid => by rw [hfr_fin, hfr_sp, hfr_pick]; exact hn_lt id hid,
      fun it hit => by rw [hfr_fin, hfr_sp, hfr_pick]; exact hi_lt it hit,
      hdisj, hwhole'_rootId, hwhole'_rank, hwhole'_nd, hwhole'_sub, hdead', hwhole'_item_nd,
      hwhole'_crk, hwhole'_all_perm, hwhole'_ck_mono, hwhole'_ck, hcur'_mem3,
      lb, hcur'_val, hframes'⟩, ?_⟩
    dsimp only [zipPhi]
    rw [zipRebuild_phi rt cur' ctx, zipRebuild_phi rt cur ctx]
    have hm_q : (memoryCost (defillStep ![itemBase, nodeBase, cur.rootId]) s : ℚ) ≤ 26 := by
      exact_mod_cast hm_step_le
    linarith

private theorem defillStep_descend_spec {rt w itemBase nodeBase : ℕ} {t₀ cur c : SHTree}
    {sib : Option SHTree} {ctx : List ZipFrame} {s s₁ s₂ s₃ : Memory.State}
    (hinv : ZipInv rt w itemBase nodeBase t₀ (some cur) ctx s)
    (hinfo : DefillCurInfo rt itemBase nodeBase t₀ cur s)
    (hps : DefillStepPSRes rt w itemBase nodeBase t₀ cur c sib s s₁ s₂ s₃)
    (hleaf : ¬ (c.left.elim 0 SHTree.rootId = 0 ∧ c.right.elim 0 SHTree.rootId = 0)) :
    DefillStepPost rt w itemBase nodeBase t₀ cur ctx s := by
  rcases hinv with ⟨h16, hmem, hn_lt, hi_lt, hdisj, hrootId, hrank, hnd, hsub, hdead, hid_nd,
    hcrk, hperm, hck_mono, hroot_ck, hcur_mem, lb, hval, hframes⟩
  rcases hinfo with ⟨hcur_sub, hcur_nd, hcur_items_sub, hcur_item_nd, hcur_root_lt,
    hcur_sz, hcur_tgt, hcur_l, hcur_r, hcur_l0_iff, hcur_r0_iff⟩
  rcases hps with ⟨hfr_pick, hmem_pick, hcsib, hc_le_sib, hcur_ne_c, hc_val, hc_mem, hcur₁_mem,
    _, _, hfr_sp, hmem_sp, hs2_0, hs2_3, hs2_45, hs2_c3, hs2_c4, hs2_c5, hwf₃, hfr_fin,
    hfin_cases, hv_step, hcost_ge5, hcap_sum, hk8_cur', hle_cur', hcur_all_perm, hsib_sub_node,
    hsib_sub_item, hs2_not_sib, hs2_not_sib_item, hs_step, hc_in_cur, hs2_frame⟩
  have hc_nonleaf : c.left.isSome ∨ c.right.isSome := by
    cases hcl : c.left <;> cases hcr : c.right
    · simp [hcl, hcr] at hleaf
    · exact Or.inr rfl
    · exact Or.inl rfl
    · exact Or.inl rfl
  have hlc := eq_false hleaf
  simp only [hlc, ↓reduceIte] at hfin_cases
  rcases hfin_cases with ⟨hm_step_le, hres_step, h3_8, hmem_fin⟩
  let f : ZipFrame := ⟨cur.rootId, cur.rank, c.ckey, cur.items ++ c.items, sib⟩
  let cur' : SHTree := .node c.rootId c.rank c.ckey [] c.left c.right
  have hframe_mem' : ∀ a, s₃.mem a ≠ s.mem a →
      (∃ id ∈ cur.nodeIds, ∃ j < 9, a = nodeBase + 12 * id + j) ∨
      (∃ it ∈ cur.items, a = itemBase + 3 * it.id + 2) := by
    intro a ha
    by_cases hfin_eq : s₃.mem a = s₂.mem a
    · rw [hfin_eq] at ha
      rcases hs2_frame a ha with ⟨id, hid, j, hj, ha'⟩ | ⟨it, hit, ha'⟩
      · exact Or.inl ⟨id, hid, j, by omega, ha'⟩
      · exact Or.inr ⟨it, hit, ha'⟩
    · by_contra hno
      exact hfin_eq (hmem_fin a (fun h => hno (Or.inl ⟨c.rootId, hc_in_cur, 8, by decide, h⟩)))
  have hframe_mem : ∀ a, s₃.mem a ≠ s.mem a →
      (∃ id ∈ t₀.nodeIds, ∃ j < 9, a = nodeBase + 12 * id + j) ∨
      (∃ it ∈ t₀.allItems, a = itemBase + 3 * it.id + 2) := by
    intro a ha
    rcases hframe_mem' a ha with ⟨id, hid, j, hj, ha'⟩ | ⟨it, hit, ha'⟩
    · exact Or.inl ⟨id, hcur_sub id hid, j, hj, ha'⟩
    · exact Or.inr ⟨it, hcur_items_sub it (by
        cases cur; dsimp only [SHTree.items] at hit; simp [SHTree.allItems_node, hit]), ha'⟩
  have hplug_nodeIds_perm : (zipPlug f cur').nodeIds.Perm cur.nodeIds := by
    refine List.Perm.trans ?_ hcur_all_perm.2.2.1
    cases c
    simp only [zipPlug, f, cur', SHTree.nodeIds_node, Option.elim_some]
    exact .refl _
  have hplug_allItems_perm : (zipPlug f cur').allItems.Perm cur.allItems := by
    refine List.Perm.trans ?_ hcur_all_perm.1
    cases c
    simp only [zipPlug, f, cur', SHTree.allItems_node, Option.elim_some, SHTree.items,
      SHTree.left, SHTree.right, List.nil_append, List.append_assoc]
    exact .refl _
  have hplug_countRank : ∀ k, (zipPlug f cur').countRank k = cur.countRank k := by
    intro k
    rw [← hcur_all_perm.2.2.2.1 k]
    cases c
    simp [zipPlug, f, cur', SHTree.countRank_node, SHTree.rank, SHTree.left, SHTree.right]
  have hwhole'_nd : (zipRebuild cur' (f :: ctx)).nodeIds.Nodup := by
    rw [zipRebuild]
    exact ((zipRebuild_nodeIds_perm (zipPlug f cur') ctx).trans
      (List.Perm.append_right _ hplug_nodeIds_perm)).nodup_iff.mpr
      ((zipRebuild_nodeIds_perm cur ctx).nodup_iff.mp hnd)
  have hwhole'_sub : ∀ id ∈ (zipRebuild cur' (f :: ctx)).nodeIds, id ∈ t₀.nodeIds := by
    intro id hid
    apply hsub id
    rw [zipRebuild] at hid
    exact (zipRebuild_nodeIds_perm cur ctx).mem_iff.mpr
      ((List.Perm.append_right _ hplug_nodeIds_perm).mem_iff.mp
        ((zipRebuild_nodeIds_perm (zipPlug f cur') ctx).mem_iff.mp hid))
  have hdead' : ∀ id ∈ t₀.nodeIds, id ∉ (zipRebuild cur' (f :: ctx)).nodeIds →
      s₃.mem (nodeBase + 12 * id + 4) = 0 := by
    intro id hid hnotin
    have hnot_old : id ∉ (zipRebuild cur ctx).nodeIds := by
      intro hin
      apply hnotin
      rw [zipRebuild]
      exact (zipRebuild_nodeIds_perm (zipPlug f cur') ctx).mem_iff.mpr
        ((List.Perm.append_right _ hplug_nodeIds_perm.symm).mem_iff.mp
          ((zipRebuild_nodeIds_perm cur ctx).mem_iff.mp hin))
    have heq_s : s₃.mem (nodeBase + 12 * id + 4) = s.mem (nodeBase + 12 * id + 4) := by
      by_contra hneq
      rcases hframe_mem' _ hneq with ⟨id', hid', _, _, _⟩ | ⟨it, hit, ha⟩
      · have : id = id' := by omega
        subst this
        exact hnot_old (zipRebuild_nodeIds_sub cur ctx _ hid')
      · exact (hdisj id hid it (hcur_items_sub it (by
          cases cur; dsimp only [SHTree.items] at hit; simp [SHTree.allItems_node, hit]))
          4 (by decide) 2 (by decide)) ha
    exact heq_s.trans (hdead id hid hnot_old)
  have hwhole'_all_perm : (zipRebuild cur' (f :: ctx)).allItems.Perm t₀.allItems := by
    rw [zipRebuild]
    exact ((((zipRebuild_allEntries_perm (zipPlug f cur') ctx).map Prod.fst).trans
      (by simp only [List.map_append]; exact List.Perm.append_right _ hplug_allItems_perm)).trans
      ((zipRebuild_allEntries_perm cur ctx).map Prod.fst).symm).trans hperm
  have hwhole'_item_nd : (zipRebuild cur' (f :: ctx)).itemIds.Nodup :=
    ((hwhole'_all_perm.trans hperm.symm).map SHItem.id).nodup_iff.mpr hid_nd
  have hwhole'_crk : ∀ k, (zipRebuild cur' (f :: ctx)).countRank k ≤ t₀.countRank k := by
    intro k
    rw [zipRebuild, zipRebuild_countRank, hplug_countRank k]
    simpa [zipRebuild_countRank] using hcrk k
  have hwhole'_ck_mono : ∀ p ∈ (zipRebuild cur' (f :: ctx)).allEntries,
      ∃ c₀, (p.1, c₀) ∈ t₀.allEntries ∧ c₀ ≤ p.2 := by
    have hc_ent : c.allEntries = c.items.map (fun it => (it, c.ckey)) ++
        c.left.elim [] SHTree.allEntries ++ c.right.elim [] SHTree.allEntries := by
      cases c
      simp [SHTree.allEntries_node, SHTree.items, SHTree.ckey, SHTree.left, SHTree.right]
    intro p hp
    rw [zipRebuild] at hp
    rcases List.mem_append.mp ((zipRebuild_allEntries_perm (zipPlug f cur') ctx).mem_iff.mp hp)
      with hp1 | hp2
    · simp only [zipPlug, f, cur', SHTree.allEntries_node, Option.elim_some, List.map_nil,
        List.nil_append, List.mem_append, List.mem_map] at hp1
      rcases hp1 with ((⟨it, hit, rfl⟩ | (hL | hR)) | hs)
      · rcases hit with h1 | h2
        · have hin : (it, cur.ckey) ∈ (zipRebuild cur ctx).allEntries :=
            (zipRebuild_allEntries_perm cur ctx).mem_iff.mpr (List.mem_append_left _ (by
              cases cur; dsimp only [SHTree.items, SHTree.ckey] at h1 ⊢
              simp [SHTree.allEntries_node, h1]))
          rcases hck_mono _ hin with ⟨c₀, hc₀, hle₀⟩
          exact ⟨c₀, hc₀, Nat.le_trans hle₀ hc_val.2.lb_le⟩
        · have hin_c : (it, c.ckey) ∈ cur.allEntries := hcur_all_perm.2.1 _ (by
            simp [SHTree.allEntries_node, hc_ent, h2])
          exact hck_mono _ ((zipRebuild_allEntries_perm cur ctx).mem_iff.mpr
            (List.mem_append_left _ hin_c))
      · exact hck_mono _ ((zipRebuild_allEntries_perm cur ctx).mem_iff.mpr
          (List.mem_append_left _ (hcur_all_perm.2.1 _ (by
            simp [SHTree.allEntries_node, hc_ent, hL]))))
      · exact hck_mono _ ((zipRebuild_allEntries_perm cur ctx).mem_iff.mpr
          (List.mem_append_left _ (hcur_all_perm.2.1 _ (by
            simp [SHTree.allEntries_node, hc_ent, hR]))))
      · exact hck_mono _ ((zipRebuild_allEntries_perm cur ctx).mem_iff.mpr
          (List.mem_append_left _ (hcur_all_perm.2.1 _ (by
            simp [SHTree.allEntries_node, hs]))))
    · exact hck_mono _ ((zipRebuild_allEntries_perm cur ctx).mem_iff.mpr
        (List.mem_append_right _ hp2))
  have hc_children_mem3 : (∀ sc, c.left = some sc → TreeMemRep rt itemBase nodeBase s₃.mem sc) ∧
      (∀ sc, c.right = some sc → TreeMemRep rt itemBase nodeBase s₃.mem sc) := by
    have hnd_c : c.nodeIds.Nodup := by
      have hp := (hcur_all_perm.2.2.1.nodup_iff.mpr hcur_nd)
      rw [SHTree.nodeIds_node, Option.elim_some, List.cons_append, List.nodup_cons] at hp
      exact (List.nodup_append.mp hp.2).1
    have hmem_c_child : ∀ ch, (c.left = some ch ∨ c.right = some ch) →
        TreeMemRep rt itemBase nodeBase s₃.mem ch := by
      intro ch hch
      have hch_mem : TreeMemRep rt itemBase nodeBase s.mem ch := by
        rcases hch with hl | hr
        · exact hc_mem.left_mem ch hl
        · exact hc_mem.right_mem ch hr
      have hch_sub_c : ∀ nid ∈ ch.nodeIds, nid ≠ cur.rootId ∧ nid ≠ c.rootId ∧
          nid ∈ cur.nodeIds := by
        intro nid hnid
        have hn_c : nid ≠ c.rootId := by
          intro heq; subst heq
          cases c with
          | node cid _ _ _ cl cr =>
            have hnd_c' := SHTree.nodeIds_head_not_mem hnd_c
            dsimp only [SHTree.left, SHTree.right] at hch
            rcases hch with rfl | rfl
            · exact hnd_c' (List.mem_append_left _ hnid)
            · exact hnd_c' (List.mem_append_right _ hnid)
        have hn_in_c : nid ∈ c.nodeIds := by
          cases c
          dsimp only [SHTree.left, SHTree.right] at hch
          rcases hch with rfl | rfl <;> simp [SHTree.nodeIds_node, hnid]
        have hn_cur : nid ≠ cur.rootId := by
          have hp := SHTree.nodeIds_head_not_mem (hcur_all_perm.2.2.1.nodup_iff.mpr hcur_nd)
          intro he
          exact hp (List.mem_append_left _ (he ▸ hn_in_c))
        have hn_cur_in : nid ∈ cur.nodeIds := hcur_all_perm.2.2.1.mem_iff.mp (by
          simp [SHTree.nodeIds_node, hn_in_c])
        exact ⟨hn_cur, hn_c, hn_cur_in⟩
      refine TreeMemRep.congr (fun nid hnid j hj => ?_) (fun it hit j hj => ?_) hch_mem
      · have hn := hch_sub_c nid hnid
        by_contra hneq
        rcases hframe_mem' _ (Ne.symm hneq) with ⟨id', hid', j', hj', ha⟩ | ⟨it, hit', ha⟩
        · have : nid = id' := by omega
          subst this
          have : j = j' := by omega
          subst this
          by_cases hs2_eq : s₂.mem (nodeBase + 12 * nid + j) = s.mem (nodeBase + 12 * nid + j)
          · exact hneq (hs2_eq.symm.trans (hmem_fin _ (by omega)).symm)
          · apply hs2_eq
            have hs1_eq : s₁.mem (nodeBase + 12 * nid + j) = s.mem (nodeBase + 12 * nid + j) :=
              hmem_pick _ (by omega) (by omega)
            rw [← hs1_eq]
            apply hmem_sp _ (by omega) (by omega) (by omega) (by omega)
              (by omega) (by omega) (by omega)
            by_cases hnil : cur.items = []
            · exact Or.inl hnil
            · right
              rcases ItemListRep.tail_mem hnil hcur₁_mem.items_rep with
                ⟨it_l, hit_l, htl_eq, _⟩
              change s₁.mem (nodeBase + 12 * cur.rootId + 5) = it_l.id at htl_eq
              rw [htl_eq]
              exact hdisj nid (hcur_sub nid hn.2.2) it_l
                (hcur_items_sub it_l (by
                  cases cur; dsimp only [SHTree.items] at hit_l
                  simp [SHTree.allItems_node, hit_l]))
                j (by omega) 2 (by decide)
        · exact (hdisj nid (hcur_sub nid hn.2.2) it
            (hcur_items_sub it (by
              cases cur; dsimp only [SHTree.items] at hit'
              simp [SHTree.allItems_node, hit']))
            j (by omega) 2 (by decide)) ha
      · have hit_in_c : it ∈ c.allItems := by
          cases c
          dsimp only [SHTree.left, SHTree.right] at hch
          rcases hch with rfl | rfl <;> simp [SHTree.allItems_node, hit]
        have hit_in_cur : it ∈ cur.allItems := hcur_all_perm.1.mem_iff.mp (by
          simp [SHTree.allItems_node, hit_in_c])
        have hit_in_t0 := hcur_items_sub it hit_in_cur
        by_contra hneq
        rcases hframe_mem' _ (Ne.symm hneq) with ⟨id', hid', j', hj', ha⟩ | ⟨it', hit', ha⟩
        · exact (hdisj id' (hcur_sub id' hid') it hit_in_t0 j' (by omega) j hj) ha.symm
        · have heq_id : it.id = it'.id := by omega
          have hc_not_cur_it : it.id ∉ (cur.items.map SHItem.id) := by
            have hnd_sw : (SHTree.node cur.rootId cur.rank cur.ckey cur.items
                (some c) sib).itemIds.Nodup :=
              (hcur_all_perm.1.map SHItem.id).nodup_iff.mpr hcur_item_nd
            simp only [SHTree.itemIds_node, Option.elim_some, List.append_assoc] at hnd_sw
            have hd1 := list_nodup_append_disj hnd_sw
            intro hin
            exact hd1.2.2 it.id hin (List.mem_append_left _ (by
              have hmem_c : it.id ∈ c.itemIds := by
                rw [SHTree.itemIds]
                exact List.mem_map_of_mem hit_in_c
              exact hmem_c))
          exact hc_not_cur_it (heq_id ▸ List.mem_map_of_mem hit')
    exact ⟨fun sc hsc => hmem_c_child sc (Or.inl hsc),
      fun sc hsc => hmem_c_child sc (Or.inr hsc)⟩
  have hcur'_mem3 : TreeMemRep rt itemBase nodeBase s₃.mem cur' := by
    have hpres : ∀ j, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 6 ∨ j = 7 →
        s₃.mem (nodeBase + 12 * c.rootId + j) = s.mem (nodeBase + 12 * c.rootId + j) := by
      intro j hj
      have hs1_eq : s₁.mem (nodeBase + 12 * c.rootId + j) = s.mem (nodeBase + 12 * c.rootId + j) :=
        hmem_pick _ (by omega) (by omega)
      have hs2_eq : s₂.mem (nodeBase + 12 * c.rootId + j) =
          s₁.mem (nodeBase + 12 * c.rootId + j) := by
        apply hmem_sp _ (by omega) (by omega) (by omega) (by omega)
          (by rcases hj with rfl | rfl | rfl | rfl | rfl <;> omega)
          (by rcases hj with rfl | rfl | rfl | rfl | rfl <;> omega)
          (by rcases hj with rfl | rfl | rfl | rfl | rfl <;> omega)
        by_cases hnil : cur.items = []
        · exact Or.inl hnil
        · right
          rcases ItemListRep.tail_mem hnil hcur₁_mem.items_rep with ⟨it_l, hit_l, htl_eq, _⟩
          change s₁.mem (nodeBase + 12 * cur.rootId + 5) = it_l.id at htl_eq
          rw [htl_eq]
          have hj_lt : j < 12 := by rcases hj with rfl | rfl | rfl | rfl | rfl <;> decide
          exact hdisj c.rootId (hcur_sub c.rootId hc_in_cur) it_l
            (hcur_items_sub it_l (by
              cases cur; dsimp only [SHTree.items] at hit_l
              simp [SHTree.allItems_node, hit_l]))
            j hj_lt 2 (by decide)
      have hj8 : j ≠ 8 := by rcases hj with rfl | rfl | rfl | rfl | rfl <;> decide
      exact (hmem_fin _ (by omega)).trans (hs2_eq.trans hs1_eq)
    have hc345 : s₃.mem (nodeBase + 12 * c.rootId + 3) = 0 ∧
        s₃.mem (nodeBase + 12 * c.rootId + 4) = 0 ∧
        s₃.mem (nodeBase + 12 * c.rootId + 5) = 0 :=
      ⟨(hmem_fin _ (by omega)).trans hs2_c3,
       (hmem_fin _ (by omega)).trans hs2_c4,
       (hmem_fin _ (by omega)).trans hs2_c5⟩
    have hc_root_ne := hc_mem.rootId_ne
    have hc_ck := hc_mem.ckey_eq
    have hc_rk := hc_mem.rank_eq
    have hc_tg := hc_mem.target_eq
    have hc_l := hc_mem.left_eq
    have hc_r := hc_mem.right_eq
    exact .node hc_root_ne ((hpres 0 (Or.inl rfl)).trans hc_ck)
      ((hpres 1 (Or.inr (Or.inl rfl))).trans hc_rk)
      ((hpres 2 (Or.inr (Or.inr (Or.inl rfl)))).trans hc_tg)
      (by simpa [cur'] using hc345.1)
      ⟨hc345.2.1, hc345.2.2⟩
      ((hpres 6 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))).trans hc_l)
      ((hpres 7 (Or.inr (Or.inr (Or.inr (Or.inr rfl))))).trans hc_r)
      hc_children_mem3.1 hc_children_mem3.2
  have hcur'_val : ZipCurValid rt f.ckey cur' :=
    ⟨by dsimp only [cur', SHTree.items, List.length_nil]; exact Nat.zero_le _, le_rfl,
      fun _ h => by simp [cur', SHTree.items] at h, fun _ _ h => by simp [cur', SHTree.items] at h,
      fun _ => hc_nonleaf, fun sc hsc => hc_val.2.left_valid sc hsc,
      fun sc hsc => hc_val.2.right_valid sc hsc⟩
  have hf_rep3 : zipFrameRep rt itemBase nodeBase s₃.mem cur' f := by
    have hsib_mem3 : ∀ sc, sib = some sc → TreeMemRep rt itemBase nodeBase s₃.mem sc := by
      intro sc hsc
      have hsib_s : TreeMemRep rt itemBase nodeBase s.mem sc := by
        rcases hcsib with ⟨_, hr⟩ | ⟨_, hl⟩
        · exact hcur_mem.right_mem sc (hr.symm ▸ hsc)
        · exact hcur_mem.left_mem sc (hl.symm ▸ hsc)
      refine TreeMemRep.congr (fun nid hnid j hj => ?_) (fun it hit j hj => ?_) hsib_s
      · have hn := hsib_sub_node nid (by simp [hsc, hnid])
        exact (hs2_not_sib nid (by simp [hsc, hnid]) j (by omega)).symm.trans
          (hmem_fin _ (by omega)).symm
      · have hit_sib : it ∈ sib.elim [] SHTree.allItems := by simp [hsc, hit]
        have hi_in := (hsib_sub_item it hit_sib).2.2
        have hd := hdisj c.rootId (hcur_sub _ hc_in_cur) it (hcur_items_sub it hi_in)
        exact (hs2_not_sib_item it hit_sib j hj).symm.trans
          (hmem_fin _ (hd 8 (by decide) j hj).symm).symm
    have hpres_cur : ∀ j, j = 1 ∨ j = 2 ∨ j = 6 ∨ j = 7 →
        s₃.mem (nodeBase + 12 * cur.rootId + j) = s₁.mem (nodeBase + 12 * cur.rootId + j) := by
      intro j hj
      have hj_lt : j < 12 := by rcases hj with rfl | rfl | rfl | rfl <;> decide
      have hs2_eq : s₂.mem (nodeBase + 12 * cur.rootId + j) =
          s₁.mem (nodeBase + 12 * cur.rootId + j) := by
        apply hmem_sp _ (by rcases hj with rfl | rfl | rfl | rfl <;> omega)
          (by rcases hj with rfl | rfl | rfl | rfl <;> omega)
          (by rcases hj with rfl | rfl | rfl | rfl <;> omega)
          (by rcases hj with rfl | rfl | rfl | rfl <;> omega)
          (by omega) (by omega) (by omega)
        by_cases hnil : cur.items = []
        · exact Or.inl hnil
        · right
          rcases ItemListRep.tail_mem hnil hcur₁_mem.items_rep with ⟨it_l, hit_l, htl_eq, _⟩
          change s₁.mem (nodeBase + 12 * cur.rootId + 5) = it_l.id at htl_eq
          rw [htl_eq]
          exact hdisj cur.rootId (hcur_sub _ cur.rootId_mem_nodeIds) it_l
            (hcur_items_sub it_l (by
              cases cur; dsimp only [SHTree.items] at hit_l
              simp [SHTree.allItems_node, hit_l]))
            j hj_lt 2 (by decide)
      exact (hmem_fin _ (by omega)).trans hs2_eq
    have hlist3 : ItemListRep itemBase s₃.mem (s₃.mem (nodeBase + 12 * cur.rootId + 4))
        (s₃.mem (nodeBase + 12 * cur.rootId + 5)) f.items := by
      rw [hmem_fin _ (by omega), hmem_fin _ (by omega)]
      refine ItemListRep.congr (fun it hit j hj => ?_) hs2_45
      have hit' : it ∈ cur.allItems := by
        rcases List.mem_append.mp hit with h1 | h2
        · cases cur; dsimp only [SHTree.items] at h1; simp [SHTree.allItems_node, h1]
        · have h2c : it ∈ c.allItems := by
            cases c; dsimp only [SHTree.items] at h2; simp [SHTree.allItems_node, h2]
          cases cur with | node _ _ _ _ _ _ =>
          rcases hcsib with ⟨hl, _⟩ | ⟨hr, _⟩
          · dsimp only [SHTree.left] at hl; simp [SHTree.allItems_node, hl, h2c]
          · dsimp only [SHTree.right] at hr; simp [SHTree.allItems_node, hr, h2c]
      have hd := hdisj c.rootId (hcur_sub c.rootId hc_in_cur) it (hcur_items_sub it hit')
      exact (hmem_fin _ (hd 8 (by decide) j hj).symm).symm
    have hc1_rk : s₁.mem (nodeBase + 12 * cur.rootId + 1) = cur.rank := hcur₁_mem.rank_eq
    have hc1_tg : s₁.mem (nodeBase + 12 * cur.rootId + 2) = targetSize rt cur.rank :=
      hcur₁_mem.target_eq
    have hc1_6 : s₁.mem (nodeBase + 12 * cur.rootId + 6) = c.rootId := hcur₁_mem.left_eq
    have hc1_7 : s₁.mem (nodeBase + 12 * cur.rootId + 7) = sib.elim 0 SHTree.rootId :=
      hcur₁_mem.right_eq
    exact ⟨hcur_mem.rootId_ne,
      (hmem_fin _ (by omega)).trans hs2_0,
      (hpres_cur 1 (Or.inl rfl)).trans hc1_rk,
      (hpres_cur 2 (Or.inr (Or.inl rfl))).trans hc1_tg,
      (hmem_fin _ (by omega)).trans hs2_3,
      hlist3,
      (hpres_cur 6 (Or.inr (Or.inr (Or.inl rfl)))).trans hc1_6,
      (hpres_cur 7 (Or.inr (Or.inr (Or.inr rfl)))).trans hc1_7,
      hsib_mem3⟩
  have hcur_8 : s.mem (nodeBase + 12 * cur.rootId + 8) =
      s₃.mem (nodeBase + 12 * (zipPlug f cur').rootId + 8) := by
    have hs3_2 : s₃.mem (nodeBase + 12 * cur.rootId + 8) =
        s₂.mem (nodeBase + 12 * cur.rootId + 8) := hmem_fin _ (by omega)
    have hs2_s : s₂.mem (nodeBase + 12 * cur.rootId + 8) =
        s.mem (nodeBase + 12 * cur.rootId + 8) := by
      by_contra hneq
      rcases hs2_frame _ hneq with ⟨_, _, _, _, ha⟩ | ⟨it, hit, ha⟩
      · omega
      · exact (hdisj cur.rootId (hcur_sub _ cur.rootId_mem_nodeIds) it
          (hcur_items_sub it (by
            cases cur; dsimp only [SHTree.items] at hit; simp [SHTree.allItems_node, hit]))
          8 (by decide) 2 (by decide)) ha
    exact (hs3_2.trans hs2_s).symm
  have hframes' : ZipFramesRep rt itemBase nodeBase s₃.mem cur' (f :: ctx) f.ckey := by
    refine ⟨h3_8, ?_, hcap_sum, hle_cur', hk8_cur', hc_val.1,
      fun sc hsc => ?_, hf_rep3, rfl, lb, Nat.le_trans hval.2.1 hc_val.2.lb_le, ?_⟩
    · intro hnil
      rcases List.append_eq_nil_iff.mp hnil with ⟨_, hc_nil⟩
      exact hc_val.2.items_ne hc_nil
    · rcases hcsib with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · have h2 := hval.2.2.2.2.2.2 sc hsc
        exact ⟨h2.1, h2.2.replace_lb (hc_le_sib sc hsc)⟩
      · have h1 := hval.2.2.2.2.2.1 sc hsc
        exact ⟨h1.1, h1.2.replace_lb (hc_le_sib sc hsc)⟩
    · exact defill_zipFrames_step hcur_sub hcur_items_sub hnd hsub hid_nd hperm hdisj
        hframe_mem' hcur_8 rfl rfl hframes
  have hwhole'_rootId : (zipRebuild cur' (f :: ctx)).rootId = t₀.rootId := by
    rw [zipRebuild, zipRebuild_rootId]
    change ctx.getLast?.elim cur.rootId ZipFrame.id = t₀.rootId
    rw [← zipRebuild_rootId]
    exact hrootId
  have hwhole'_rank : (zipRebuild cur' (f :: ctx)).rank = t₀.rank := by
    rw [zipRebuild]
    cases ctx with
    | nil => simpa [zipRebuild, zipPlug, f, SHTree.rank] using hrank
    | cons g rest =>
      have := (zipRebuild_rank cur (g :: rest)).2 g rest rfl
      have := (zipRebuild_rank (zipPlug f cur') (g :: rest)).2 g rest rfl
      omega
  have hwhole'_ck : t₀.items ≠ [] → t₀.ckey ≤ (zipRebuild cur' (f :: ctx)).ckey := by
    intro hne
    rw [zipRebuild]
    cases ctx with
    | nil =>
      simp only [zipRebuild] at hroot_ck ⊢
      exact Nat.le_trans (hroot_ck hne) hc_val.2.lb_le
    | cons g rest =>
      simp only [zipRebuild] at hroot_ck ⊢
      rw [zipRebuild_ckey_of_cons (zipPlug f cur') cur g rest]
      exact hroot_ck hne
  have hphi_drop : (zipPlug f cur').phi rt + 60 ≤ cur.phi rt := by
    rw [← hcur_all_perm.2.2.2.2]
    have hc_half : targetSize rt c.rank ≤ 2 * c.items.length :=
      hc_val.2.half_full hc_nonleaf
    have hc_rank1 : cur.rank = c.rank + 1 := hc_val.1.symm
    cases c with | node cid crk cck citems cl cr =>
    dsimp only [SHTree.rank, SHTree.items] at hc_half hc_rank1
    have hts_pos : (0 : ℚ) < (targetSize rt crk : ℚ) := by
      exact_mod_cast targetSize_pos rt crk
    have hhalf_q : (1 : ℚ) / 2 ≤ (citems.length : ℚ) / (targetSize rt crk : ℚ) := by
      rw [div_le_div_iff₀ (by decide) hts_pos]
      have : (targetSize rt crk : ℚ) ≤ 2 * (citems.length : ℚ) := by exact_mod_cast hc_half
      linarith
    have hsub := itemPhi_sub_succ rt crk
    simp only [zipPlug, f, cur', SHTree.phi, SHTree.itemPhiSum_node, SHTree.nodeCount_node,
      Option.elim_some, SHTree.items, SHTree.rank, SHTree.left, SHTree.right,
      List.length_append, List.length_nil, Nat.cast_zero, zero_mul, zero_add, hc_rank1]
    have h120 :
        (60 : ℚ) ≤ 120 * ((citems.length : ℚ) * (itemPhi rt crk - itemPhi rt (crk + 1))) := by
      rw [hsub]
      have : (120 : ℚ) * ((citems.length : ℚ) * (1 / (targetSize rt crk : ℚ))) =
          120 * ((citems.length : ℚ) / (targetSize rt crk : ℚ)) := by ring
      rw [this]
      linarith
    push_cast at h120 ⊢
    linarith
  unfold DefillStepPost
  refine ⟨hv_step, some cur', f :: ctx, ?_, ?_, ?_, hcost_ge5, ?_⟩
  · dsimp only [cur', SHTree.rootId]; exact hres_step
  · rw [hs_step]; exact hfr_fin.trans (hfr_sp.trans hfr_pick)
  · rw [hs_step]; exact hframe_mem
  · rw [hs_step]
    refine ⟨⟨h16, hwf₃,
      fun id hid => by rw [hfr_fin, hfr_sp, hfr_pick]; exact hn_lt id hid,
      fun it hit => by rw [hfr_fin, hfr_sp, hfr_pick]; exact hi_lt it hit,
      hdisj, hwhole'_rootId, hwhole'_rank, hwhole'_nd, hwhole'_sub, hdead', hwhole'_item_nd,
      hwhole'_crk, hwhole'_all_perm, hwhole'_ck_mono, hwhole'_ck, hcur'_mem3,
      f.ckey, hcur'_val, hframes'⟩, ?_⟩
    dsimp only [zipPhi]
    rw [zipRebuild_phi rt cur' (f :: ctx), zipRebuild_phi rt cur ctx]
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have hplug_eq : (zipPlug f cur').phi rt =
        cur'.phi rt + (120 * ((f.items.length : ℚ) * itemPhi rt f.rank +
          f.sibling.elim 0 (SHTree.itemPhiSum rt)) +
          30 * ((1 + f.sibling.elim 0 SHTree.nodeCount : ℕ) : ℚ)) := by
      simp [zipPlug, SHTree.phi, SHTree.itemPhiSum_node, SHTree.nodeCount_node]; ring
    have hm_q : (memoryCost (defillStep ![itemBase, nodeBase, cur.rootId]) s : ℚ) ≤ 24 := by
      exact_mod_cast hm_step_le
    push_cast at hplug_eq ⊢
    linarith

private theorem defillStep_ascend_spec {rt w itemBase nodeBase : ℕ} {t₀ cur : SHTree}
    {ctx : List ZipFrame} {s : Memory.State}
    (hinv : ZipInv rt w itemBase nodeBase t₀ (some cur) ctx s)
    (hinfo : DefillCurInfo rt itemBase nodeBase t₀ cur s)
    (hc_cond : ¬ (cur.items.length < targetSize rt cur.rank ∧
      (cur.left.isSome ∨ cur.right.isSome))) :
    DefillStepPost rt w itemBase nodeBase t₀ cur ctx s := by
  rcases hinv with ⟨h16, hmem, hn_lt, hi_lt, hdisj, hrootId, hrank, hnd, hsub, hdead, hid_nd,
    hcrk, hperm, hck_mono, hroot_ck, hcur_mem, _, hval, hframes⟩
  rcases hinfo with ⟨_, _, _, _, hcur_root_lt,
    hcur_sz, hcur_tgt, hcur_l, hcur_r, hcur_l0_iff, hcur_r0_iff⟩
  have hcond_mem : ¬ (s.mem (nodeBase + 12 * cur.rootId + 3) <
      s.mem (nodeBase + 12 * cur.rootId + 2) ∧
      (s.mem (nodeBase + 12 * cur.rootId + 6) ≠ 0 ∨
        s.mem (nodeBase + 12 * cur.rootId + 7) ≠ 0)) := by
    rw [hcur_sz, hcur_tgt, hcur_l0_iff, hcur_r0_iff]; exact hc_cond
  have hcond_f := eq_false hcond_mem
  have hcur_valid_full := ZipCurValid.toValid (rt := rt) hval
    (zipCurValid_items_ne_empty_of_not_cond hval hc_cond).1
    (zipCurValid_items_ne_empty_of_not_cond hval hc_cond).2
  have hv_step : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (defillStep ![itemBase, nodeBase, cur.rootId])) := by
    dsimp only [defillStep]
    simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    refine validHistory_read_bind (by omega) (validHistory_read_bind (by omega)
      (validHistory_read_bind (by omega) (validHistory_read_bind (by omega) ?_)))
    simp only [hcond_f, ↓reduceIte]
    exact validHistory_read (by omega)
  have hcost_eq : memoryCost (defillStep ![itemBase, nodeBase, cur.rootId]) s = 5 := by
    dsimp only [defillStep]
    simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    repeat (rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read])
    simp only [hcond_f, ↓reduceIte, memoryCost_read]
  have hs_eq : (Memory.spec 0).clientState s (defillStep ![itemBase, nodeBase, cur.rootId]) =
      s := by
    dsimp only [defillStep]
    simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    repeat rw [clientState_bind_read]
    simp only [hcond_f, ↓reduceIte]
    rfl
  have hres_eq : (Memory.spec 0).clientResult s (defillStep ![itemBase, nodeBase, cur.rootId]) =
      s.mem (nodeBase + 12 * cur.rootId + 8) := by
    dsimp only [defillStep]
    simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    repeat rw [clientResult_bind_read]
    simp only [hcond_f, ↓reduceIte]
    rfl
  cases ctx with
  | nil =>
    rcases hframes with ⟨h8, rfl⟩
    refine ⟨hv_step, none, [], ?_, ?_, fun a hne => ?_, by omega, ?_⟩
    · simp only [Option.elim_none]; rw [hres_eq, h8]
    · rw [hs_eq]
    · rw [hs_eq] at hne; exact absurd rfl hne
    · rw [hs_eq]
      refine ⟨⟨h16, hmem, hn_lt, hi_lt, hdisj, rfl, cur,
        by simpa [zipRebuild] using hrootId, by simpa [zipRebuild] using hrank,
        hcur_valid_full, (zipCurValid_items_ne_empty_of_not_cond hval hc_cond).2,
        fun hne => by simpa [zipRebuild] using hroot_ck hne, by simpa [zipRebuild] using hnd,
        by simpa [zipRebuild] using hsub, by simpa [zipRebuild] using hdead,
        by simpa [zipRebuild] using hcrk, by simpa [zipRebuild] using hperm,
        by simpa [zipRebuild] using hck_mono, hcur_mem, h8⟩, ?_, rfl,
        by simpa [zipRebuild] using hrootId, by simpa [zipRebuild] using hrank,
        hcur_valid_full, (zipCurValid_items_ne_empty_of_not_cond hval hc_cond).2,
        fun hne => by simpa [zipRebuild] using hroot_ck hne, by simpa [zipRebuild] using hnd,
        by simpa [zipRebuild] using hsub, by simpa [zipRebuild] using hdead,
        by simpa [zipRebuild] using hcrk, by simpa [zipRebuild] using hperm,
        by simpa [zipRebuild] using hck_mono, hcur_mem, h8⟩
      unfold zipPhi
      simp only [hcost_eq, zipRebuild, List.length_nil, Nat.cast_zero, mul_zero, add_zero]
      push_cast
      linarith
  | cons f rest =>
    rcases hframes with ⟨h8, hf_ne, hf_cap, hf_le, hf_k8, hf_rk, hf_sib, hf_rep, rfl, lb',
      hlb', hrest⟩
    refine ⟨hv_step, some (zipPlug f cur), rest, ?_, ?_, fun a hne => ?_, by omega, ?_⟩
    · simp only [Option.elim_some, zipPlug]; rw [hres_eq, h8]; rfl
    · rw [hs_eq]
    · rw [hs_eq] at hne; exact absurd rfl hne
    · rw [hs_eq]
      refine ⟨⟨h16, hmem, hn_lt, hi_lt, hdisj, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_⟩, ?_⟩
      · simpa [zipRebuild] using hrootId
      · simpa [zipRebuild] using hrank
      · simpa [zipRebuild] using hnd
      · simpa [zipRebuild] using hsub
      · simpa [zipRebuild] using hdead
      · simpa [zipRebuild] using hid_nd
      · simpa [zipRebuild] using hcrk
      · simpa [zipRebuild] using hperm
      · simpa [zipRebuild] using hck_mono
      · simpa [zipRebuild] using hroot_ck
      · exact .node hf_rep.1 hf_rep.2.1 hf_rep.2.2.1 hf_rep.2.2.2.1 hf_rep.2.2.2.2.1
          hf_rep.2.2.2.2.2.1 hf_rep.2.2.2.2.2.2.1 hf_rep.2.2.2.2.2.2.2.1
          (fun _ hc => by cases hc; exact hcur_mem) hf_rep.2.2.2.2.2.2.2.2
      · refine ⟨lb', ⟨hf_cap, hlb', hf_le, hf_k8, fun hn => absurd hn hf_ne,
          fun _ hc => by cases hc; exact ⟨hf_rk, hcur_valid_full⟩, hf_sib⟩, hrest⟩
      · unfold zipPhi
        simp only [hcost_eq, zipRebuild, List.length_cons]
        push_cast
        linarith

private theorem defillStep_spec {rt w itemBase nodeBase : ℕ} {t₀ cur : SHTree}
    {ctx : List ZipFrame} {s : Memory.State}
    (hinv : ZipInv rt w itemBase nodeBase t₀ (some cur) ctx s) :
    let d : Fin 3 → ℕ := ![itemBase, nodeBase, cur.rootId]
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (defillStep d)) ∧
    ∃ (cur?' : Option SHTree) (ctx' : List ZipFrame),
      let res := (Memory.spec 0).clientResult s (defillStep d)
      let s' := (Memory.spec 0).clientState s (defillStep d)
      res = cur?'.elim 0 SHTree.rootId ∧
      s'.frontier = s.frontier ∧
      (∀ a, s'.mem a ≠ s.mem a →
        (∃ id ∈ t₀.nodeIds, ∃ j < 9, a = nodeBase + 12 * id + j) ∨
        (∃ it ∈ t₀.allItems, a = itemBase + 3 * it.id + 2)) ∧
      5 ≤ memoryCost (defillStep d) s ∧
      match cur?' with
      | none =>
          ZipInv rt w itemBase nodeBase t₀ none [] s' ∧
          (memoryCost (defillStep d) s : ℚ) + cur.phi rt ≤ zipPhi rt (some cur) ctx ∧
          ctx = [] ∧
          cur.rootId = t₀.rootId ∧ cur.rank = t₀.rank ∧ cur.Valid rt 0 ∧
          (cur.left.isSome ∨ cur.right.isSome → targetSize rt cur.rank ≤ cur.items.length) ∧
          (t₀.items ≠ [] → t₀.ckey ≤ cur.ckey) ∧
          cur.nodeIds.Nodup ∧ (∀ id ∈ cur.nodeIds, id ∈ t₀.nodeIds) ∧
          (∀ id ∈ t₀.nodeIds, id ∉ cur.nodeIds → s'.mem (nodeBase + 12 * id + 4) = 0) ∧
          (∀ k, cur.countRank k ≤ t₀.countRank k) ∧
          cur.allItems.Perm t₀.allItems ∧
          (∀ p ∈ cur.allEntries, ∃ c₀, (p.1, c₀) ∈ t₀.allEntries ∧ c₀ ≤ p.2) ∧
          TreeMemRep rt itemBase nodeBase s'.mem cur ∧
          s'.mem (nodeBase + 12 * cur.rootId + 8) = 0
      | some cur' =>
          ZipInv rt w itemBase nodeBase t₀ (some cur') ctx' s' ∧
          (memoryCost (defillStep d) s : ℚ) + zipPhi rt (some cur') ctx' ≤
            zipPhi rt (some cur) ctx := by
  change DefillStepPost rt w itemBase nodeBase t₀ cur ctx s
  have hinfo := defillCurInfo_of_zipInv hinv
  by_cases hc_cond : cur.items.length < targetSize rt cur.rank ∧
      (cur.left.isSome ∨ cur.right.isSome)
  · rcases defillStep_ps_spec hinv hinfo hc_cond with ⟨c, sib, s₁, s₂, s₃, hps⟩
    by_cases hleaf : c.left.elim 0 SHTree.rootId = 0 ∧ c.right.elim 0 SHTree.rootId = 0
    · exact defillStep_leaf_spec hinv hinfo hps hleaf
    · exact defillStep_descend_spec hinv hinfo hps hleaf
  · exact defillStep_ascend_spec hinv hinfo hc_cond


private theorem defill_while_spec {rt w itemBase nodeBase : ℕ} {t₀ : SHTree}
    (fuel : ℕ) {cur : SHTree} {ctx : List ZipFrame} {s : Memory.State}
    (hinv : ZipInv rt w itemBase nodeBase t₀ (some cur) ctx s)
    (hfuel : ⌊zipPhi rt (some cur) ctx / 5⌋₊ ≤ fuel)
    (hf_fit : Fits w fuel) :
    let prog := boundedWhile (fun (_ : Unit) (x : ℕ) => x ≠ 0)
      (fun x => defillStep ![itemBase, nodeBase, x.2]) () fuel cur.rootId
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    whileSafe (fun (_ : Unit) (x : ℕ) => x ≠ 0)
      (fun x => defillStep ![itemBase, nodeBase, x.2]) (fun w _ _ => Fits w 16)
      w () fuel cur.rootId s ∧
    let s' := (Memory.spec 0).clientState s prog
    s'.frontier = s.frontier ∧
    (∀ a, s'.mem a ≠ s.mem a →
      (∃ id ∈ t₀.nodeIds, ∃ j < 9, a = nodeBase + 12 * id + j) ∨
      (∃ it ∈ t₀.allItems, a = itemBase + 3 * it.id + 2)) ∧
    ∃ t',
      t'.rootId = t₀.rootId ∧
      t'.rank = t₀.rank ∧
      t'.Valid rt 0 ∧
      (t'.left.isSome ∨ t'.right.isSome → targetSize rt t'.rank ≤ t'.items.length) ∧
      (t₀.items ≠ [] → t₀.ckey ≤ t'.ckey) ∧
      t'.nodeIds.Nodup ∧
      (∀ id ∈ t'.nodeIds, id ∈ t₀.nodeIds) ∧
      (∀ id ∈ t₀.nodeIds, id ∉ t'.nodeIds → s'.mem (nodeBase + 12 * id + 4) = 0) ∧
      (∀ k, t'.countRank k ≤ t₀.countRank k) ∧
      t'.allItems.Perm t₀.allItems ∧
      (∀ p ∈ t'.allEntries, ∃ c₀, (p.1, c₀) ∈ t₀.allEntries ∧ c₀ ≤ p.2) ∧
      TreeMemRep rt itemBase nodeBase s'.mem t' ∧
      s'.mem (nodeBase + 12 * t'.rootId + 8) = 0 ∧
      (memoryCost prog s : ℚ) + t'.phi rt ≤ zipPhi rt (some cur) ctx := by
  induction fuel generalizing cur ctx s with
  | zero =>
    have hphi : 5 ≤ zipPhi rt (some cur) ctx := by
      unfold zipPhi
      have := (zipRebuild cur ctx).phi_nonneg rt
      have : (0 : ℚ) ≤ (ctx.length : ℚ) := Nat.cast_nonneg _
      linarith
    have h1 : (1 : ℚ) ≤ zipPhi rt (some cur) ctx / 5 := by linarith
    have hfl : 1 ≤ ⌊zipPhi rt (some cur) ctx / 5⌋₊ := Nat.le_floor h1
    omega
  | succ fuel' ih =>
    have h16 : Fits w 16 := hinv.1
    have hcur_ne : cur.rootId ≠ 0 := by
      rcases hinv with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hcm, _, _, _⟩
      exact hcm.rootId_ne
    have hstep := defillStep_spec hinv
    rcases hstep with ⟨hv_step, cur?', ctx', hres, hfr₁, hframe₁, hm_ge5, hmatch⟩
    set s₁ := (Memory.spec 0).clientState s (defillStep ![itemBase, nodeBase, cur.rootId])
    cases cur?' with
    | none =>
      rcases hmatch with ⟨_, hphi_le, rfl, hrootId, hrank, hval, hpop, hck, hnd, hsub, hdead,
        hcrk, hperm, hck_mono, hmem_rep, h8⟩
      simp only [Option.elim_none] at hres
      have hbw : boundedWhile (fun (_ : Unit) (x : ℕ) => x ≠ 0)
          (fun x => defillStep ![itemBase, nodeBase, x.2]) () (fuel' + 1) cur.rootId =
          (do let a' ← defillStep ![itemBase, nodeBase, cur.rootId]
              boundedWhile (fun (_ : Unit) (x : ℕ) => x ≠ 0)
                (fun x => defillStep ![itemBase, nodeBase, x.2]) () fuel' a') := by
        simp [boundedWhile, hcur_ne]
      have hbw_nil : ∀ m, boundedWhile (fun (_ : Unit) (x : ℕ) => x ≠ 0)
          (fun x => defillStep ![itemBase, nodeBase, x.2]) () m 0 = pure 0 := fun m =>
        boundedWhile_of_not _ _ _ _ _ (by simp)
      have hs_prog : (Memory.spec 0).clientState s
          (boundedWhile (fun (_ : Unit) (x : ℕ) => x ≠ 0)
            (fun x => defillStep ![itemBase, nodeBase, x.2]) () (fuel' + 1) cur.rootId) = s₁ := by
        rw [hbw, StateTransitionSpec.clientState_bind, hres, hbw_nil]
        rfl
      dsimp only
      refine ⟨?_, ?_, ?_, ?_, cur, hrootId, hrank, hval, hpop, hck, hnd, hsub, ?_,
        hcrk, hperm, hck_mono, ?_, ?_, ?_⟩
      · rw [hbw]
        refine validHistory_bind_step hv_step ?_
        rw [hres, hbw_nil]
        exact validHistory_pure w _ _
      · exact whileSafe_succ_pos hcur_ne h16 (by rw [hres]; exact whileSafe_of_not (by simp))
      · rw [hs_prog]; exact hfr₁
      · intro a ha; rw [hs_prog] at ha; exact hframe₁ a ha
      · intro id hid hnot; rw [hs_prog]; exact hdead id hid hnot
      · rw [hs_prog]; exact hmem_rep
      · rw [hs_prog]; exact h8
      · rw [hbw, memoryCost_bind', hres, hbw_nil, memoryCost_pure, add_zero]
        exact hphi_le
    | some cur' =>
      rcases hmatch with ⟨hinv', hphi_step⟩
      simp only [Option.elim_some] at hres
      have hdrop : zipPhi rt (some cur') ctx' / 5 + 1 ≤ zipPhi rt (some cur) ctx / 5 := by
        have hm_q : (5 : ℚ) ≤
            (memoryCost (defillStep ![itemBase, nodeBase, cur.rootId]) s : ℚ) := by
          exact_mod_cast hm_ge5
        linarith
      have hfl' : ⌊zipPhi rt (some cur') ctx' / 5⌋₊ ≤ fuel' := by
        have hfl_le : (⌊zipPhi rt (some cur') ctx' / 5⌋₊ : ℚ) ≤ zipPhi rt (some cur') ctx' / 5 :=
          Nat.floor_le (div_nonneg (zipPhi_nonneg rt (some cur') ctx') (by decide))
        have hle_fl : ⌊zipPhi rt (some cur') ctx' / 5⌋₊ + 1 ≤ ⌊zipPhi rt (some cur) ctx / 5⌋₊ := by
          apply Nat.le_floor
          push_cast
          linarith
        omega
      have hih := ih hinv' hfl' (hf_fit.of_le (by omega))
      rcases hih with ⟨hv_ih, hsafe_ih, hfr_ih, hframe_ih, t', hrootId, hrank, hval, hpop, hck,
        hnd, hsub, hdead, hcrk, hperm, hck_mono, hmem_rep, h8, hphi_ih⟩
      have hbw : boundedWhile (fun (_ : Unit) (x : ℕ) => x ≠ 0)
          (fun x => defillStep ![itemBase, nodeBase, x.2]) () (fuel' + 1) cur.rootId =
          (do let a' ← defillStep ![itemBase, nodeBase, cur.rootId]
              boundedWhile (fun (_ : Unit) (x : ℕ) => x ≠ 0)
                (fun x => defillStep ![itemBase, nodeBase, x.2]) () fuel' a') := by
        simp [boundedWhile, hcur_ne]
      have hs_prog : (Memory.spec 0).clientState s
          (boundedWhile (fun (_ : Unit) (x : ℕ) => x ≠ 0)
            (fun x => defillStep ![itemBase, nodeBase, x.2]) () (fuel' + 1) cur.rootId) =
          (Memory.spec 0).clientState s₁
            (boundedWhile (fun (_ : Unit) (x : ℕ) => x ≠ 0)
              (fun x => defillStep ![itemBase, nodeBase, x.2]) () fuel' cur'.rootId) := by
        rw [hbw, StateTransitionSpec.clientState_bind, hres]
      dsimp only
      refine ⟨?_, ?_, ?_, ?_, t', hrootId, hrank, hval, hpop, hck, hnd, hsub, ?_,
        hcrk, hperm, hck_mono, ?_, ?_, ?_⟩
      · rw [hbw]
        refine validHistory_bind_step hv_step ?_
        rw [hres]
        exact hv_ih
      · exact whileSafe_succ_pos hcur_ne h16 (by rw [hres]; exact hsafe_ih)
      · rw [hs_prog]; exact hfr_ih.trans hfr₁
      · intro a ha
        rw [hs_prog] at ha
        by_cases h1 : s₁.mem a = s.mem a
        · rw [← h1] at ha
          exact hframe_ih a ha
        · exact hframe₁ a h1
      · intro id hid hnot; rw [hs_prog]; exact hdead id hid hnot
      · rw [hs_prog]; exact hmem_rep
      · rw [hs_prog]; exact h8
      · rw [hbw, memoryCost_bind', hres]
        push_cast
        linarith

/-- Full specification of `defill`: starting from a root tree `t₀` satisfying `ZipCurValid 0 t₀`,
`defill` produces a valid refilled tree `t'` satisfying `popDeficit rt t' = 0`, modifies only cells
inside `t₀` (`+0..+8` on `t₀.nodeIds` and `+2` on `t₀.allItems`), zeroes `head` on deleted leaves,
and spends `memoryCost + t'.phi rt ≤ t₀.phi rt + 6`. -/
theorem defill_spec {rt w itemBase nodeBase fuel : ℕ} {t₀ : SHTree} {s : Memory.State}
    (h16 : Fits w 16) (hmem : Memory.WellFormed w s)
    (hval₀ : ZipCurValid rt 0 t₀)
    (hnd₀ : t₀.nodeIds.Nodup) (hid₀ : t₀.itemIds.Nodup)
    (hmem₀ : TreeMemRep rt itemBase nodeBase s.mem t₀)
    (hn_lt : ∀ id ∈ t₀.nodeIds, nodeBase + 12 * id + 11 < s.frontier)
    (hi_lt : ∀ it ∈ t₀.allItems, itemBase + 3 * it.id + 2 < s.frontier)
    (hdisj : ∀ id ∈ t₀.nodeIds, ∀ it ∈ t₀.allItems, ∀ j < 12, ∀ k < 3,
      nodeBase + 12 * id + j ≠ itemBase + 3 * it.id + k)
    (hf_fit : Fits w fuel)
    (hfuel : t₀.phi rt + 5 ≤ 5 * (fuel : ℚ)) :
    let d : Fin 4 → ℕ := ![itemBase, nodeBase, t₀.rootId, fuel]
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (defill d)) ∧
    defillSafe w d s ∧
    let s' := (Memory.spec 0).clientState s (defill d)
    s'.frontier = s.frontier ∧
    (∀ a, s'.mem a ≠ s.mem a →
      (∃ id ∈ t₀.nodeIds, ∃ j < 9, a = nodeBase + 12 * id + j) ∨
      (∃ it ∈ t₀.allItems, a = itemBase + 3 * it.id + 2)) ∧
    ∃ t',
      t'.rootId = t₀.rootId ∧
      t'.rank = t₀.rank ∧
      t'.Valid rt 0 ∧
      popDeficit rt t' = 0 ∧
      (t₀.items ≠ [] → t₀.ckey ≤ t'.ckey) ∧
      t'.nodeIds.Nodup ∧
      (∀ id ∈ t'.nodeIds, id ∈ t₀.nodeIds) ∧
      (∀ id ∈ t₀.nodeIds, id ∉ t'.nodeIds → s'.mem (nodeBase + 12 * id + 4) = 0) ∧
      (∀ k, t'.countRank k ≤ t₀.countRank k) ∧
      t'.allItems.Perm t₀.allItems ∧
      (∀ p ∈ t'.allEntries, ∃ c₀, (p.1, c₀) ∈ t₀.allEntries ∧ c₀ ≤ p.2) ∧
      TreeMemRep rt itemBase nodeBase s'.mem t' ∧
      (memoryCost (defill d) s : ℚ) + t'.phi rt ≤ t₀.phi rt + 6 := by
  have hroot_lt : nodeBase + 12 * t₀.rootId + 11 < s.frontier :=
    hn_lt t₀.rootId t₀.rootId_mem_nodeIds
  have h0_fit : Fits w 0 := h16.of_le (by omega)
  set s₁ : Memory.State := ⟨Function.update s.mem (nodeBase + 12 * t₀.rootId + 8) 0, s.frontier⟩
  have hwf₁ : Memory.WellFormed w s₁ :=
    hmem.step (o := .write (nodeBase + 12 * t₀.rootId + 8) 0) ⟨by omega, h0_fit⟩
  have hmem₁ : TreeMemRep rt itemBase nodeBase s₁.mem t₀ := by
    refine TreeMemRep.congr (fun id hid j hj => ?_) (fun it hit j hj => ?_) hmem₀
    · dsimp only [s₁]; exact (Function.update_of_ne (by omega) _ _).symm
    · dsimp only [s₁]
      exact (Function.update_of_ne
        ((hdisj t₀.rootId t₀.rootId_mem_nodeIds it hit 8 (by decide) j hj).symm) _ _).symm
  have hinv₁ : ZipInv rt w itemBase nodeBase t₀ (some t₀) [] s₁ := by
    refine ⟨h16, hwf₁, fun id hid => hn_lt id hid, fun it hit => hi_lt it hit, hdisj,
      rfl, rfl, hnd₀, fun _ h => h, fun _ _ h => absurd ‹_› h, hid₀, fun _ => le_rfl,
      .refl _, fun p hp => ⟨p.2, hp, le_rfl⟩, fun _ => le_rfl, hmem₁, 0, hval₀, ?_, rfl⟩
    simp [s₁]
  have hfl : ⌊zipPhi rt (some t₀) [] / 5⌋₊ ≤ fuel := by
    apply Nat.floor_le_of_le
    unfold zipPhi
    simp only [zipRebuild, List.length_nil, Nat.cast_zero, mul_zero, add_zero]
    linarith
  have hbw := defill_while_spec fuel hinv₁ hfl hf_fit
  rcases hbw with ⟨hv_bw, hsafe_bw, hfr_bw, hframe_bw, t', hrootId, hrank, hval, hpop, hck,
    hnd', hsub', hdead', hcrk', hperm', hck_mono, hmem_rep', _, hphi_bw⟩
  have hs_defill : (Memory.spec 0).clientState s (defill ![itemBase, nodeBase, t₀.rootId, fuel]) =
      (Memory.spec 0).clientState s₁ (boundedWhile (fun (_ : Unit) (x : ℕ) => x ≠ 0)
        (fun x => defillStep ![itemBase, nodeBase, x.2]) () fuel t₀.rootId) := by
    dsimp only [defill]
    simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    rw [clientState_bind_write, StateTransitionSpec.clientState_bind]
    rfl
  have hm_defill : memoryCost (defill ![itemBase, nodeBase, t₀.rootId, fuel]) s =
      1 + memoryCost (boundedWhile (fun (_ : Unit) (x : ℕ) => x ≠ 0)
        (fun x => defillStep ![itemBase, nodeBase, x.2]) () fuel t₀.rootId) s₁ := by
    dsimp only [defill]
    simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    rw [memoryCost_bind', memoryCost_write, clientState_write, memoryCost_bind',
      memoryCost_pure, add_zero]
  dsimp only
  refine ⟨?_, ⟨h16, hsafe_bw⟩, ?_, ?_, t', hrootId, hrank, hval, ?_, hck, hnd', hsub', ?_,
    hcrk', hperm', hck_mono, ?_, ?_⟩
  · dsimp only [defill]
    simp +decide only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    exact validHistory_write_bind (by omega) h0_fit (validHistory_bind_step hv_bw
      (validHistory_pure w _ _))
  · rw [hs_defill]; exact hfr_bw
  · intro a ha
    rw [hs_defill] at ha
    by_cases heq : a = nodeBase + 12 * t₀.rootId + 8
    · exact Or.inl ⟨t₀.rootId, t₀.rootId_mem_nodeIds, 8, by decide, heq⟩
    · by_cases h1 : ((Memory.spec 0).clientState s₁
          (boundedWhile (fun (_ : Unit) (x : ℕ) => x ≠ 0)
            (fun x => defillStep ![itemBase, nodeBase, x.2]) () fuel t₀.rootId)).mem a = s₁.mem a
      · have hs1_eq : s₁.mem a = s.mem a := Function.update_of_ne heq _ _
        exact absurd (h1.trans hs1_eq) ha
      · exact hframe_bw a h1
  · unfold popDeficit
    split_ifs with hch
    · have := hpop hch
      simp [Nat.min_eq_right this]
    · rfl
  · intro id hid hnot; rw [hs_defill]; exact hdead' id hid hnot
  · rw [hs_defill]; exact hmem_rep'
  · rw [hm_defill]
    unfold zipPhi at hphi_bw
    simp only [zipRebuild, List.length_nil, Nat.cast_zero, mul_zero, add_zero] at hphi_bw
    push_cast
    linarith

end Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap
