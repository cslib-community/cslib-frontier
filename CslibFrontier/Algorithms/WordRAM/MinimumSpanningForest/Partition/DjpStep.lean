/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.Partition.DjpOps
public import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.Contraction.Robust
import CslibFrontier.Computability.WordRAM.Realization.LoopFrame
import CslibFrontier.Computability.WordRAM.Realization.ArrayOps
import CslibFrontier.DataStructure.Memory.Frame
import CslibFrontier.DataStructure.PriorityQueue.WordRAM.SoftHeap.Insert
import CslibFrontier.Tactic.UpdateSimp
import CslibFrontier.Tactic.ValidProg
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Zify

/-!
# Setup, CSR, Dynamic-DJP Tree, and Soft-Heap Expansion Specifications

Verifies helper invariants (`remDeg`, `djpVertsList`, `extendDJP`), stride-4 writers
(`partWriteStride4_spec`, `partCopyIndexedEdge_spec`), workspace initialization (`partSetup_spec`),
and Soft-Heap incident-edge expansion (`partTryInsertEdge_spec`, `partExpandVertex_iter_spec`,
`partExpandVertex_spec`) for the `ε = 1 / 16` (`partRankThreshold = 8`) dynamic DJP partition
subroutine.

## Main definitions

* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.remDeg`: remaining CSR degree sum outside
  vertex set `S`.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.djpVertsList`: ordered vertex list
  `[root, vOut 0, ..., vOut (numSteps - 1)]` of a `DynamicDJPTree`.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.extendDJP`: extends a `DynamicDJPTree` by one
  popped cross edge `(vIn, vOut)`.

## Main results

* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.partWriteStride4_spec`,
  `partCopyIndexedEdge_spec`, `partSetup_spec`: setup and stride-4 edge-copy specifications.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.partTryInsertEdge_spec`,
  `partExpandVertex_iter_spec`, `partExpandVertex_spec`: Soft-Heap edge insertion and vertex
  expansion specifications with `2450`-per-half-edge amortized cost bound.
-/

public section

namespace Cslib.Algorithms.WordRAM.MinimumSpanningForest

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.Algorithms.Lean.Kruskal Cslib.Query.MinimumSpanningForest
open Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap

/-! ## Soft-Heap Forest, CSR, Memory Framing, and Dynamic-DJP Helpers -/

/-- Item membership in `forestItems roots` iff paired with some corrupted key in
`forestEntries roots`. -/
private theorem mem_forestItems_iff {it : SHItem} {roots : List SHTree} :
    it ∈ forestItems roots ↔ ∃ c, (it, c) ∈ forestEntries roots := by
  simp [forestItems, Prod.exists]

/-- Live item count in `forestItems roots` is at most `h.itemCount - ic₀`. -/
theorem shInv_forestItems_length_le {w ic₀ nc₀ maxItems maxNodes : ℕ}
    {h : SHHandle} {roots : List SHTree} {created : ℕ → ℕ} {s : Memory.State}
    (hinv : SHInv w ic₀ nc₀ maxItems maxNodes h roots created s) :
    (forestItems roots).length ≤ h.itemCount - ic₀ := by
  have hlen : (forestItemIds roots).length = (forestItems roots).length := by
    simp [forestItemIds, forestItems, forestEntries, SHTree.itemIds, SHTree.allItems]
  have hnd : ((forestItemIds roots).map (fun id => id - (ic₀ + 1))).Nodup := by
    refine List.Nodup.map_on ?_ hinv.itemIds_nodup
    intro a ha b hb _
    have ha' := (hinv.itemIds_range a ha).1
    have hb' := (hinv.itemIds_range b hb).1
    omega
  have hsub : ((forestItemIds roots).map (fun id => id - (ic₀ + 1))).toFinset ⊆
      Finset.range (h.itemCount - ic₀) := by
    intro y hy
    rw [List.mem_toFinset, List.mem_map] at hy
    rcases hy with ⟨id, hid, rfl⟩
    have hid' := hinv.itemIds_range id hid
    exact Finset.mem_range.mpr (by omega)
  calc (forestItems roots).length = (forestItemIds roots).length := hlen.symm
    _ = ((forestItemIds roots).map (fun id => id - (ic₀ + 1))).length := by simp
    _ = ((forestItemIds roots).map (fun id => id - (ic₀ + 1))).toFinset.card :=
      (List.toFinset_card_of_nodup hnd).symm
    _ ≤ (Finset.range (h.itemCount - ic₀)).card := Finset.card_le_card hsub
    _ = h.itemCount - ic₀ := Finset.card_range _

/-- Total CSR degree sum across `Fin n` equals `2 * es.length`. -/
private theorem csr_deg_sum_eq {n : ℕ} {offBase adjBase : ℕ} {es : List (IndexedEdge n)}
    {mem : ℕ → ℕ} (hcsr : HoldsUndirCSR offBase adjBase es mem) :
    (∑ u : Fin n, (mem (offBase + u.val + 1) - mem (offBase + u.val))) = 2 * es.length := by
  have hsum : ∀ k ≤ n, (∀ j < k, mem (offBase + j) ≤ mem (offBase + j + 1)) →
      (∑ i : Fin k, (mem (offBase + i.val + 1) - mem (offBase + i.val))) =
        mem (offBase + k) - mem offBase := by
    intro k
    induction k with
    | zero => intro _ _; simp
    | succ k ih =>
      intro hk hmono
      rw [Fin.sum_univ_castSucc]
      have hk1 := ih (by omega) fun j hj => hmono j (by omega)
      have hle_last := hmono k (Nat.lt_succ_self k)
      have h0_le : mem offBase ≤ mem (offBase + k) := by
        clear hk1 hle_last hk ih
        induction k with
        | zero => simp
        | succ m ihm =>
          have h1 := hmono m (by omega)
          have h2 := ihm (fun j hj => hmono j (by omega))
          rw [show offBase + (m + 1) = offBase + m + 1 by omega]
          omega
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [show offBase + (k + 1) = offBase + k + 1 by omega]
      omega
  have hdeg := hsum n (le_refl n) fun j hj => hcsr.off_mono ⟨j, hj⟩
  rw [hcsr.off_zero, hcsr.off_end, Nat.sub_zero] at hdeg
  exact hdeg

/-- Remaining CSR half-edge degree sum over vertices outside `S`. -/
@[expose] def remDeg (n offBase : ℕ) (mem : ℕ → ℕ) (S : Finset (Fin n)) : ℕ :=
  ∑ u : Fin n, if u ∈ S then 0 else mem (offBase + u.val + 1) - mem (offBase + u.val)

/-- Empty vertex set leaves all `2 * es.length` CSR half-edges unexpanded. -/
theorem remDeg_empty {n offBase adjBase : ℕ} {es : List (IndexedEdge n)} {mem : ℕ → ℕ}
    (hcsr : HoldsUndirCSR offBase adjBase es mem) :
    remDeg n offBase mem ∅ = 2 * es.length := by
  dsimp only [remDeg]
  simp only [Finset.notMem_empty, ↓reduceIte]
  exact csr_deg_sum_eq hcsr

/-- Inserting a fresh vertex `x ∉ S` subtracts `deg(x)` from `remDeg`. -/
theorem remDeg_insert {n offBase : ℕ} {mem : ℕ → ℕ} {S : Finset (Fin n)}
    {x : Fin n} (hx : x ∉ S) :
    remDeg n offBase mem (insert x S) + (mem (offBase + x.val + 1) - mem (offBase + x.val)) =
      remDeg n offBase mem S := by
  dsimp only [remDeg]
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ x)]
  conv_rhs => rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ x)]
  simp only [Finset.mem_insert_self, ↓reduceIte, hx, zero_add]
  have hrest :
      (∑ u ∈ Finset.univ.erase x,
        if u ∈ insert x S then 0 else mem (offBase + u.val + 1) - mem (offBase + u.val)) =
      (∑ u ∈ Finset.univ.erase x,
        if u ∈ S then 0 else mem (offBase + u.val + 1) - mem (offBase + u.val)) := by
    refine Finset.sum_congr rfl fun u hu => ?_
    have hne : u ≠ x := Finset.ne_of_mem_erase hu
    simp [Finset.mem_insert, hne]
  rw [hrest]; omega

/-- Congruence lemma for `remDeg` when offsets agree on `[offBase, offBase + n]`. -/
theorem remDeg_congr {n offBase : ℕ} {m₁ m₂ : ℕ → ℕ} (S : Finset (Fin n))
    (hagree : ∀ k ≤ n, m₂ (offBase + k) = m₁ (offBase + k)) :
    remDeg n offBase m₂ S = remDeg n offBase m₁ S := by
  dsimp only [remDeg]
  refine Finset.sum_congr rfl fun u _ => ?_
  have h1 := hagree u.val (by omega)
  have h2 := hagree (u.val + 1) (by omega)
  rw [← Nat.add_assoc] at h2
  rw [h1, h2]

/-- Antitonicity of `remDeg` with respect to vertex-set inclusion. -/
theorem remDeg_anti {n offBase : ℕ} {mem : ℕ → ℕ} {S T : Finset (Fin n)} (hsub : S ⊆ T) :
    remDeg n offBase mem T ≤ remDeg n offBase mem S := by
  dsimp only [remDeg]
  refine Finset.sum_le_sum fun u _ => ?_
  by_cases huT : u ∈ T
  · simp [huT]
  · have huS : u ∉ S := fun hs => huT (hsub hs)
    simp [huT, huS]

/-- Extracts out-of-set memory agreement from `Memory.Modifies` and preserved frontier. -/
private theorem mem_eq_of_modifies_frontier {α : Type} {w : ℕ} {S : Set ℕ} {s : Memory.State}
    {prog : Memory.Prog α}
    (hv : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog))
    (hmod : Memory.Modifies S s ((Memory.spec 0).clientState s prog))
    (hfr : ((Memory.spec 0).clientState s prog).frontier = s.frontier) :
    ∀ x, x ∉ S → ((Memory.spec 0).clientState s prog).mem x = s.mem x := by
  intro x hxS
  by_cases hx : x < s.frontier
  · exact hmod.2 x hx hxS
  · have ha : ((Memory.spec w).clientState s prog).frontier ≤ x := by
      rw [clientState_width w, hfr]; omega
    simpa only [clientState_width w] using Memory.mem_clientState_of_frontier_le s prog hv ha

/-- Builds `Memory.Modifies S` from unchanged frontier and outside agreement. -/
private theorem modifies_of_agree_outside (S : Set ℕ) {s s' : Memory.State}
    (hfr : s'.frontier = s.frontier) (hagree : ∀ x, x ∉ S → s'.mem x = s.mem x) :
    Memory.Modifies S s s' :=
  ⟨le_of_eq hfr.symm, fun x _ hx => hagree x hx⟩

/-- Ordered vertex list `[root, vOut 0, ..., vOut (numSteps - 1)]` of `D`. -/
@[expose] def djpVertsList {n : ℕ} (D : DynamicDJPTree n) : List (Fin n) :=
  D.root :: (List.finRange D.numSteps).map D.vOut

/-- Length of `djpVertsList D` equals `D.numSteps + 1`. -/
theorem djpVertsList_length {n : ℕ} (D : DynamicDJPTree n) :
    (djpVertsList D).length = D.numSteps + 1 := by
  simp [djpVertsList]

/-- Membership characterization for `D.treeVerts k` (`k ≤ D.numSteps`). -/
private theorem mem_djpVerts_iff_mem_list {n : ℕ} (D : DynamicDJPTree n) :
    ∀ k ≤ D.numSteps, ∀ x : Fin n,
      x ∈ D.treeVerts k ↔ x = D.root ∨ ∃ j : Fin D.numSteps, j.val < k ∧ D.vOut j = x := by
  intro k hk x
  induction k with
  | zero => simp [DynamicDJPTree.treeVerts, djpVerts]
  | succ k ih =>
    dsimp only [DynamicDJPTree.treeVerts, djpVerts]
    have hk_lt : k < D.numSteps := Nat.lt_of_succ_le hk
    simp only [hk_lt, ↓reduceDIte, Finset.mem_insert]
    rw [ih (Nat.le_of_lt hk_lt)]
    constructor
    · rintro (rfl | rfl | ⟨j, hj, rfl⟩)
      · exact .inr ⟨⟨k, hk_lt⟩, Nat.lt_succ_self k, rfl⟩
      · exact .inl rfl
      · exact .inr ⟨j, Nat.lt_succ_of_lt hj, rfl⟩
    · rintro (rfl | ⟨j, hj, rfl⟩)
      · exact .inr (.inl rfl)
      · by_cases hj_eq : j.val = k
        · exact .inl (by rw [show j = ⟨k, hk_lt⟩ from Fin.ext hj_eq])
        · exact .inr (.inr ⟨j, by omega, rfl⟩)

/-- Membership in `djpVertsList D` iff membership in `D.treeVerts D.numSteps`. -/
theorem mem_djpVertsList_iff {n : ℕ} (D : DynamicDJPTree n) (x : Fin n) :
    x ∈ djpVertsList D ↔ x ∈ D.treeVerts D.numSteps := by
  rw [mem_djpVerts_iff_mem_list D D.numSteps le_rfl x]
  simp only [djpVertsList, List.mem_cons, List.mem_map, List.mem_finRange, true_and]
  constructor
  · rintro (rfl | ⟨j, hj⟩)
    · exact .inl rfl
    · exact .inr ⟨j, j.isLt, hj⟩
  · rintro (rfl | ⟨j, _, hj⟩)
    · exact .inl rfl
    · exact .inr ⟨j, hj⟩

/-- Cardinality of `D.treeVerts k` is `k + 1` for `k ≤ D.numSteps`. -/
theorem djpVerts_card {n : ℕ} (D : DynamicDJPTree n) :
    ∀ k ≤ D.numSteps, (D.treeVerts k).card = k + 1 := by
  intro k hk
  induction k with
  | zero => simp [DynamicDJPTree.treeVerts, djpVerts]
  | succ k ih =>
    have hkn : k < D.numSteps := Nat.lt_of_succ_le hk
    dsimp only [DynamicDJPTree.treeVerts, djpVerts]
    simp only [hkn, ↓reduceDIte]
    rw [Finset.card_insert_of_notMem (D.vOut_not_mem ⟨k, hkn⟩), ih hkn.le]

/-- Any `DynamicDJPTree` visits at most `n` distinct vertices (`D.numSteps + 1 ≤ n`). -/
theorem djp_numSteps_add_one_le {n : ℕ} (D : DynamicDJPTree n) :
    D.numSteps + 1 ≤ n := by
  calc D.numSteps + 1 = (D.treeVerts D.numSteps).card := (djpVerts_card D D.numSteps le_rfl).symm
    _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_univ _
    _ = n := Fintype.card_fin n

/-- `djpVertsList D` has no duplicate vertices. -/
theorem djpVertsList_nodup {n : ℕ} (D : DynamicDJPTree n) :
    (djpVertsList D).Nodup := by
  have hv_mem : ∀ k : Fin D.numSteps, D.vOut k ∈ D.treeVerts (k.val + 1) := by
    intro k
    rw [mem_djpVerts_iff_mem_list D (k.val + 1) k.isLt]
    exact .inr ⟨k, Nat.lt_succ_self _, rfl⟩
  have hroot_mem : ∀ k ≤ D.numSteps, D.root ∈ D.treeVerts k := fun k hk => by
    rw [mem_djpVerts_iff_mem_list D k hk]; exact .inl rfl
  have hinj : Function.Injective D.vOut := by
    intro i j hij
    rcases lt_trichotomy i.val j.val with hlt | heq | hgt
    · have him := mem_djpVerts_mono D.root D.vOut hlt (hv_mem i)
      rw [hij] at him; exact absurd him (D.vOut_not_mem j)
    · exact Fin.ext heq
    · have hjm := mem_djpVerts_mono D.root D.vOut hgt (hv_mem j)
      rw [← hij] at hjm; exact absurd hjm (D.vOut_not_mem i)
  refine List.nodup_cons.mpr ⟨?_, (List.nodup_finRange D.numSteps).map hinj⟩
  intro hmem
  simp only [List.mem_map, List.mem_finRange, true_and] at hmem
  rcases hmem with ⟨k, hk⟩
  have hr := hroot_mem k.val k.isLt.le
  rw [← hk] at hr
  exact D.vOut_not_mem k hr

/-- `(k + 1)`-th entry of `djpVertsList D` is `D.vOut k`. -/
theorem djpVertsList_getElem_succ {n : ℕ} (D : DynamicDJPTree n) (k : Fin D.numSteps) :
    (djpVertsList D)[k.val + 1]'(by rw [djpVertsList_length]; omega) = D.vOut k := by
  simp [djpVertsList]

private theorem djpVerts_extend_eq {n : ℕ} (D : DynamicDJPTree n) (vOut : Fin n) :
    ∀ m ≤ D.numSteps,
      djpVerts D.root (fun k' : Fin (D.numSteps + 1) =>
        if hk' : k'.val < D.numSteps then D.vOut ⟨k'.val, hk'⟩ else vOut) m =
      D.treeVerts m := by
  intro m hm_le
  induction m with
  | zero => rfl
  | succ m ih =>
    dsimp only [djpVerts, DynamicDJPTree.treeVerts] at ih ⊢
    have hlt : m < D.numSteps := Nat.lt_of_succ_le hm_le
    simp only [Nat.lt_succ_of_lt hlt, ↓reduceDIte, hlt]
    rw [ih hlt.le]

/-- Appends one popped cross edge `(vIn, vOut)` to a `DynamicDJPTree`. -/
@[expose] def extendDJP {n : ℕ} (D : DynamicDJPTree n) (e : IndexedEdge n) (wPop : ℕ)
    (vIn vOut : Fin n) (hew : e.weight ≤ wPop)
    (hm : (e.u = vIn ∧ e.v = vOut) ∨ (e.v = vIn ∧ e.u = vOut))
    (hvin : vIn ∈ D.treeVerts D.numSteps) (hvout : vOut ∉ D.treeVerts D.numSteps)
    (hfut : ∀ s : Fin D.numSteps,
      (e.u ∈ D.treeVerts s.val ↔ e.v ∉ D.treeVerts s.val) → D.wPop s ≤ wPop) :
    DynamicDJPTree n where
  numSteps := D.numSteps + 1
  root := D.root
  edge k := if hk : k.val < D.numSteps then D.edge ⟨k.val, hk⟩ else e.toWeighted
  wPop k := if hk : k.val < D.numSteps then D.wPop ⟨k.val, hk⟩ else wPop
  vIn k := if hk : k.val < D.numSteps then D.vIn ⟨k.val, hk⟩ else vIn
  vOut k := if hk : k.val < D.numSteps then D.vOut ⟨k.val, hk⟩ else vOut
  edge_weight_le_wPop k := by
    split_ifs with hk
    · exact D.edge_weight_le_wPop ⟨k.val, hk⟩
    · exact hew
  ends_match k := by
    split_ifs with hk
    · exact D.ends_match ⟨k.val, hk⟩
    · exact hm
  vIn_mem k := by
    split_ifs with hk
    · rw [djpVerts_extend_eq D vOut k.val hk.le]; exact D.vIn_mem ⟨k.val, hk⟩
    · have hk_eq : k.val = D.numSteps := by omega
      rw [hk_eq, djpVerts_extend_eq D vOut D.numSteps le_rfl]; exact hvin
  vOut_not_mem k := by
    split_ifs with hk
    · rw [djpVerts_extend_eq D vOut k.val hk.le]; exact D.vOut_not_mem ⟨k.val, hk⟩
    · have hk_eq : k.val = D.numSteps := by omega
      rw [hk_eq, djpVerts_extend_eq D vOut D.numSteps le_rfl]; exact hvout
  djp_future s s' hlt hcross := by
    have hs_lt : s.val < D.numSteps := by omega
    rw [djpVerts_extend_eq D vOut s.val hs_lt.le] at hcross
    simp only [hs_lt, ↓reduceDIte]
    split_ifs with hs'
    · simp only [hs', ↓reduceDIte] at hcross
      exact D.djp_future ⟨s.val, hs_lt⟩ ⟨s'.val, hs'⟩ hlt hcross
    · simp only [hs', ↓reduceDIte] at hcross
      exact hfut ⟨s.val, hs_lt⟩ hcross

/-- Prefix vertex sets of `extendDJP` agree with `D` for `k ≤ D.numSteps`. -/
theorem extendDJP_treeVerts_le {n : ℕ} (D : DynamicDJPTree n) (e : IndexedEdge n)
    (wPop : ℕ) (vIn vOut : Fin n) (hew hm hvin hvout hfut) (k : ℕ) (hk : k ≤ D.numSteps) :
    (extendDJP D e wPop vIn vOut hew hm hvin hvout hfut).treeVerts k = D.treeVerts k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hlt : k < D.numSteps := Nat.lt_of_succ_le hk
    dsimp only [DynamicDJPTree.treeVerts, djpVerts, extendDJP]
    simp only [Nat.lt_succ_of_lt hlt, ↓reduceDIte, hlt]
    exact congrArg (insert (D.vOut ⟨k, hlt⟩)) (ih hlt.le)

/-- Final vertex set of `extendDJP` inserts `vOut` into `D.treeVerts D.numSteps`. -/
theorem extendDJP_treeVerts_succ {n : ℕ} (D : DynamicDJPTree n) (e : IndexedEdge n)
    (wPop : ℕ) (vIn vOut : Fin n) (hew hm hvin hvout hfut) :
    (extendDJP D e wPop vIn vOut hew hm hvin hvout hfut).treeVerts (D.numSteps + 1) =
      insert vOut (D.treeVerts D.numSteps) := by
  change djpVerts (extendDJP D e wPop vIn vOut hew hm hvin hvout hfut).root
    (extendDJP D e wPop vIn vOut hew hm hvin hvout hfut).vOut (D.numSteps + 1) = _
  rw [djpVerts]
  have hlt : D.numSteps < (extendDJP D e wPop vIn vOut hew hm hvin hvout hfut).numSteps :=
    Nat.lt_succ_self _
  simp only [hlt, ↓reduceDIte]
  have hv : (extendDJP D e wPop vIn vOut hew hm hvin hvout hfut).vOut ⟨D.numSteps, hlt⟩ =
      vOut := by
    simp [extendDJP]
  rw [hv]
  exact congrArg (insert vOut)
    (extendDJP_treeVerts_le D e wPop vIn vOut hew hm hvin hvout hfut D.numSteps le_rfl)

/-- Tree edge list of `extendDJP` appends `e.toWeighted` to `D.treeEdges`. -/
theorem extendDJP_treeEdges {n : ℕ} (D : DynamicDJPTree n) (e : IndexedEdge n)
    (wPop : ℕ) (vIn vOut : Fin n) (hew hm hvin hvout hfut) :
    (extendDJP D e wPop vIn vOut hew hm hvin hvout hfut).treeEdges =
      D.treeEdges ++ [e.toWeighted] := by
  dsimp only [DynamicDJPTree.treeEdges]
  refine List.ext_getElem (by simp [extendDJP]) fun i hi1 hi2 => ?_
  simp only [List.length_map, List.length_finRange, extendDJP] at hi1
  by_cases hi : i < D.numSteps
  · simp [extendDJP, hi, List.getElem_append_left]
  · have hieq : i = D.numSteps := by omega
    subst hieq
    simp [extendDJP, List.getElem_append_right]

/-- Extracting one item from a nodup Soft-Heap forest preserves edge-ID uniqueness. -/
theorem forestItems_nodup_of_perm {it₀ : SHItem} {roots₁ roots₀ : List SHTree}
    (hperm : (it₀ :: forestItems roots₁).Perm (forestItems roots₀))
    (hnd : ((forestItems roots₀).map SHItem.val).Nodup) :
    ((forestItems roots₁).map SHItem.val).Nodup := by
  rw [← (hperm.map SHItem.val).nodup_iff, List.map_cons] at hnd
  exact (List.nodup_cons.mp hnd).2

/-- Any item from `roots₀` other than popped edge `eIdx` survives into `roots'`. -/
theorem forest_mem_of_pop_ne {m : ℕ} {it₀ : SHItem} {roots₀ roots₁ roots' : List SHTree}
    {eIdx e' : Fin m} {p₀ : SHItem × ℕ}
    (hperm : (it₀ :: forestItems roots₁).Perm (forestItems roots₀))
    (hkeep : ∀ it ∈ forestItems roots₁, it ∈ forestItems roots')
    (he_id : it₀.val = eIdx.val) (hp₀ : p₀ ∈ forestEntries roots₀) (hp₀_id : p₀.1.val = e'.val)
    (hne : e' ≠ eIdx) : ∃ p ∈ forestEntries roots', p.1.val = e'.val := by
  rcases List.mem_cons.mp (hperm.symm.subset (mem_forestItems_iff.mpr ⟨p₀.2, hp₀⟩)) with
    rfl | hmem1
  · exact absurd (Fin.ext (hp₀_id.symm.trans he_id)) hne
  · rcases mem_forestItems_iff.mp (hkeep p₀.1 hmem1) with ⟨c', hc'⟩
    exact ⟨(p₀.1, c'), hc', hp₀_id⟩

/-! ## Stride-4 Writers and `partSetup` Specification -/

/-- Specification of `partWriteStride4`: writes `(a, b, c, eid)` at `dst + 4 * idx` in cost `4`. -/
theorem partWriteStride4_spec {w dst idx a b c eid : ℕ} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hfa : Fits w a) (hfb : Fits w b) (hfc : Fits w c) (hfid : Fits w eid)
    (hlt : dst + 4 * idx + 3 < s.frontier) :
    let prog := partWriteStride4 ⟨dst, idx, a, b, c, eid⟩
    let s' := (Memory.spec 0).clientState s prog
    partWriteStride4Safe w ⟨dst, idx, a, b, c, eid⟩ s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    memoryCost prog s = 4 ∧
    s'.frontier = s.frontier ∧
    Memory.WellFormed w s' ∧
    (∀ x, ¬(dst + 4 * idx ≤ x ∧ x < dst + 4 * idx + 4) → s'.mem x = s.mem x) ∧
    s'.mem (dst + 4 * idx) = a ∧ s'.mem (dst + 4 * idx + 1) = b ∧
    s'.mem (dst + 4 * idx + 2) = c ∧ s'.mem (dst + 4 * idx + 3) = eid := by
  have hfront := hwf.frontier_fits
  have hprog_w : partWriteStride4 ⟨dst, idx, a, b, c, eid⟩ =
      (Memory.write (dst + 4 * idx) a >>= fun _ =>
        Memory.write (dst + 4 * idx + 1) b >>= fun _ =>
          Memory.write (dst + 4 * idx + 2) c >>= fun _ =>
            Memory.write (dst + 4 * idx + 3) eid) := partWriteStride4_def _
  have hvh : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (partWriteStride4 ⟨dst, idx, a, b, c, eid⟩)) := by
    rw [hprog_w]
    exact validHistory_write_bind (by omega) hfa (validHistory_write_bind (by simp; omega) hfb
      (validHistory_write_bind (by simp; omega) hfc (validHistory_write (by simp; omega) hfid)))
  have hcost : memoryCost (partWriteStride4 ⟨dst, idx, a, b, c, eid⟩) s = 4 := by
    rw [hprog_w, memoryCost_bind', memoryCost_write, clientState_write,
      memoryCost_bind', memoryCost_write, clientState_write,
      memoryCost_bind', memoryCost_write, memoryCost_write]
  have hst : (Memory.spec 0).clientState s (partWriteStride4 ⟨dst, idx, a, b, c, eid⟩) =
      ⟨Function.update (Function.update (Function.update (Function.update s.mem
        (dst + 4 * idx) a) (dst + 4 * idx + 1) b) (dst + 4 * idx + 2) c)
        (dst + 4 * idx + 3) eid, s.frontier⟩ := by
    rw [hprog_w, clientState_bind_write, clientState_bind_write, clientState_bind_write]; rfl
  refine ⟨by rw [partWriteStride4Safe_def]; exact ⟨h16, hlt⟩, hvh, hcost, by rw [hst],
    wellFormed_clientState hwf hvh, fun x hx => ?_, ?_, ?_, ?_, ?_⟩
  · rw [hst]; dsimp only
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  · rw [hst]; dsimp only
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_self]
  · rw [hst]; dsimp only
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
  · rw [hst]; dsimp only; rw [Function.update_of_ne (by omega), Function.update_self]
  · rw [hst]; dsimp only; rw [Function.update_self]

/-- Specification of `partCopyIndexedEdge`: copies one stride-4 edge from `srcBase + 4 * srcIdx`
to `dstBase + 4 * dstIdx` in cost `8` while framing other memory cells. -/
theorem partCopyIndexedEdge_spec {w srcBase dstBase srcIdx dstIdx : ℕ} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hs_lt : srcBase + 4 * srcIdx + 3 < s.frontier)
    (hd_lt : dstBase + 4 * dstIdx + 3 < s.frontier) :
    let prog := partCopyIndexedEdge ⟨srcBase, dstBase, srcIdx, dstIdx⟩
    let s' := (Memory.spec 0).clientState s prog
    partCopyIndexedEdgeSafe w ⟨srcBase, dstBase, srcIdx, dstIdx⟩ s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    memoryCost prog s ≤ 8 ∧
    s'.frontier = s.frontier ∧
    Memory.WellFormed w s' ∧
    (∀ a, ¬(dstBase + 4 * dstIdx ≤ a ∧ a < dstBase + 4 * dstIdx + 4) → s'.mem a = s.mem a) ∧
    (s'.mem (dstBase + 4 * dstIdx) = s.mem (srcBase + 4 * srcIdx) ∧
     s'.mem (dstBase + 4 * dstIdx + 1) = s.mem (srcBase + 4 * srcIdx + 1) ∧
     s'.mem (dstBase + 4 * dstIdx + 2) = s.mem (srcBase + 4 * srcIdx + 2) ∧
     s'.mem (dstBase + 4 * dstIdx + 3) = s.mem (srcBase + 4 * srcIdx + 3)) := by
  have hfront := hwf.frontier_fits
  have hws := partWriteStride4_spec h16 hwf (hwf.mem_fits (srcBase + 4 * srcIdx))
    (hwf.mem_fits (srcBase + 4 * srcIdx + 1)) (hwf.mem_fits (srcBase + 4 * srcIdx + 2))
    (hwf.mem_fits (srcBase + 4 * srcIdx + 3)) hd_lt
  rcases hws with ⟨_, hvh_w, hm_w, hfr_w, hwf_w, hmod_w, h0, h1, h2, h3⟩
  have hvh : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s
        (partCopyIndexedEdge ⟨srcBase, dstBase, srcIdx, dstIdx⟩)) := by
    rw [partCopyIndexedEdge_def]
    dsimp only
    refine validHistory_read_bind (by omega) (validHistory_read_bind (by omega)
      (validHistory_read_bind (by omega) (validHistory_read_bind (by omega) hvh_w)))
  have hcost : memoryCost (partCopyIndexedEdge ⟨srcBase, dstBase, srcIdx, dstIdx⟩) s ≤ 8 := by
    rw [partCopyIndexedEdge_def]
    dsimp only
    rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
      memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
      memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
      memoryCost_bind', memoryCost_read, clientResult_read, clientState_read, hm_w]
  have hst_eq : (Memory.spec 0).clientState s
      (partCopyIndexedEdge ⟨srcBase, dstBase, srcIdx, dstIdx⟩) =
      (Memory.spec 0).clientState s (partWriteStride4 ⟨dstBase, dstIdx,
        s.mem (srcBase + 4 * srcIdx), s.mem (srcBase + 4 * srcIdx + 1),
        s.mem (srcBase + 4 * srcIdx + 2), s.mem (srcBase + 4 * srcIdx + 3)⟩) := by
    rw [partCopyIndexedEdge_def]
    dsimp only
    rw [clientState_bind_read, clientState_bind_read, clientState_bind_read, clientState_bind_read]
  refine ⟨by rw [partCopyIndexedEdgeSafe_def]; exact ⟨h16, hs_lt, hd_lt⟩, hvh, hcost,
    by rw [hst_eq]; exact hfr_w, by rw [hst_eq]; exact hwf_w,
    fun a ha => by rw [hst_eq]; exact hmod_w a ha,
    by rw [hst_eq]; exact h0, by rw [hst_eq]; exact h1,
    by rw [hst_eq]; exact h2, by rw [hst_eq]; exact h3⟩

/-- Specification of `partSetup`: constructs CSR, allocates Soft-Heap pool (`rankThreshold = 8`),
zeros initial `dead`, `inCur`, and `edgeState` arrays, and yields a validated `PartLayout`. -/
theorem partSetup_spec {w n edgeBase maxsize : ℕ} {es : List (IndexedEdge n)}
    {s : Memory.State} (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hn_pos : 1 ≤ n) (hmax_pos : 1 ≤ maxsize)
    (hin : HoldsIndexedEdges edgeBase es s.mem)
    (hin_lt : edgeBase + 4 * es.length ≤ s.frontier)
    (hfit : Fits w (s.frontier + 1100 * (es.length + n + 1))) :
    let prog := partSetup ⟨n, es.length, edgeBase, maxsize⟩
    let res := (Memory.spec 0).clientResult s prog
    let s' := (Memory.spec 0).clientState s prog
    partSetupSafe w ⟨n, es.length, edgeBase, maxsize⟩ s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    memoryCost prog s ≤ 17 * es.length + 8 * n + 9 ∧
    res.env.n = n ∧ res.env.m = es.length ∧ res.env.edgeBase = edgeBase ∧
    res.env.maxsize = maxsize ∧
    res.env.bufBase = s.frontier + (2 * n + 4 * es.length + 1) +
      (3 * (2 * es.length + 1) + 12 * (4 * es.length + 1)) ∧
    res.sh = ⟨res.sh.itemBase, res.sh.nodeBase, 0, 0, 0, partRankThreshold⟩ ∧
    s'.frontier = res.env.bufBase + (14 * n + 14 * es.length) ∧
    Memory.WellFormed w s' ∧
    (∀ a < s.frontier, s'.mem a = s.mem a) ∧
    HoldsIndexedEdges edgeBase es s'.mem ∧
    HoldsUndirCSR res.env.offBase res.env.adjBase es s'.mem ∧
    SHInv w 0 0 (2 * es.length) (4 * es.length) res.sh [] (fun _ => 0) s' ∧
    (∀ j < 2 * n, s'.mem (res.env.bufBase + j) = 0) ∧
    (∀ j < es.length, s'.mem (res.env.bufBase + 14 * n + j) = 0) ∧
    ∃ L : PartLayout w n,
      L.toEnv = res.env ∧ L.es = es ∧ L.edgeBase = edgeBase ∧ L.maxsize = maxsize ∧
      L.offBase = res.env.offBase ∧ L.adjBase = res.env.adjBase ∧
      L.itemBase = res.sh.itemBase ∧ L.nodeBase = res.sh.nodeBase ∧
      L.bufBase = res.env.bufBase ∧ L.initFrontier = s.frontier := by
  let m := es.length
  have hfit_csr : Fits w (s.frontier + (2 * n + 4 * m + 1)) := hfit.of_le (by omega)
  obtain ⟨hv_csr, hm_csr, hmod_csr, hcsr1, hcsr2, hfr1, hwf1, hcsr_hold⟩ :=
    framedTriple_iff_realization.mp (buildUndirCSR_spec h16 hwf hin hin_lt hfit_csr)
  set csr := (Memory.spec 0).clientResult s (buildUndirCSR ⟨n, m, edgeBase⟩)
  set s1 := (Memory.spec 0).clientState s (buildUndirCSR ⟨n, m, edgeBase⟩)
  have hfit_pool : Fits w (s1.frontier + 3 * (2 * m + 1) + 12 * (4 * m + 1) + 16) := by
    rw [hfr1]; exact hfit.of_le (by omega)
  obtain ⟨hv_pool, hm_pool, hp1, hp2, hfr2, hmod2, hwf2⟩ := allocPool_spec hwf1 hfit_pool
  set pool := (Memory.spec 0).clientResult s1 (allocPool (2 * m) (4 * m))
  set s2 := (Memory.spec 0).clientState s1 (allocPool (2 * m) (4 * m))
  let bufBase := s2.frontier
  let s3 : Memory.State := ⟨s2.mem, bufBase + (14 * n + 14 * m)⟩
  have hfit_buf : Fits w (bufBase + (14 * n + 14 * m)) := by
    dsimp only [bufBase]; rw [hfr2, hfr1]; exact hfit.of_le (by omega)
  have hwf3 : Memory.WellFormed w s3 := ⟨hfit_buf, fun a => hwf2.mem_fits a⟩
  have h2n : Fits w (2 * n) := hfit.of_le (by omega)
  have hm : Fits w m := hfit.of_le (by omega)
  have h0_fit : Fits w 0 := h16.of_le (by omega)
  obtain ⟨hv_z1, hm_z1, hmod_z1, hfr4, hwf4, hval4⟩ := framedTriple_iff_realization.mp
    (fillConstProg_spec (base := bufBase) (val := 0) (count := 2 * n) hwf3 h0_fit h2n
      (by dsimp only [s3]; omega))
  set s4 := (Memory.spec 0).clientState s3 (fillConstProg bufBase 0 (2 * n))
  obtain ⟨hv_z2, hm_z2, hmod_z2, hfr5, hwf5, hval5⟩ := framedTriple_iff_realization.mp
    (fillConstProg_spec (base := bufBase + 14 * n) (val := 0) (count := m) hwf4 h0_fit hm
      (by rw [hfr4]; dsimp only [s3]; omega))
  set s5 := (Memory.spec 0).clientState s4 (fillConstProg (bufBase + 14 * n) 0 m)
  have hagree_z1 : ∀ x, x ∉ Set.Ico bufBase (bufBase + 2 * n) → s4.mem x = s3.mem x :=
    mem_eq_of_modifies_frontier hv_z1 hmod_z1 hfr4
  have hagree_z2 : ∀ x, x ∉ Set.Ico (bufBase + 14 * n) (bufBase + 14 * n + m) →
      s5.mem x = s4.mem x :=
    mem_eq_of_modifies_frontier hv_z2 hmod_z2 hfr5
  have hv_all : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (partSetup ⟨n, m, edgeBase, maxsize⟩)) := by
    rw [partSetup_def]
    refine validHistory_bind_step hv_csr (validHistory_bind_step hv_pool ?_)
    exact validHistory_allocDirty_bind hfit_buf
      (validHistory_bind_step hv_z1 (validHistory_bind_step hv_z2 (validHistory_pure w _ _)))
  have hcost_all : memoryCost (partSetup ⟨n, m, edgeBase, maxsize⟩) s ≤ 17 * m + 8 * n + 9 := by
    rw [partSetup_def]
    rw [memoryCost_bind', memoryCost_bind', memoryCost_bind',
      memoryCost_allocDirty, clientResult_allocDirty, clientState_allocDirty,
      memoryCost_bind', memoryCost_bind', memoryCost_pure]
    have hcsr_m : memoryCost (buildUndirCSR ⟨n, m, edgeBase⟩) s ≤ 16 * m + 5 * n + 6 := hm_csr
    have hpool_m : memoryCost (allocPool (2 * m) (4 * m)) s1 = 2 := hm_pool
    have hz1_m : memoryCost (fillConstProg bufBase 0 (2 * n)) s3 ≤ 2 * n := hm_z1
    have hz2_m : memoryCost (fillConstProg (bufBase + 14 * n) 0 m) s4 ≤ m := hm_z2
    change memoryCost (buildUndirCSR ⟨n, m, edgeBase⟩) s +
      (memoryCost (allocPool (2 * m) (4 * m)) s1 + (1 + (memoryCost (fillConstProg bufBase 0
        (2 * n)) s3 + (memoryCost (fillConstProg (bufBase + 14 * n) 0 m) s4 + 0)))) ≤ _
    omega
  have hres_eq : (Memory.spec 0).clientResult s (partSetup ⟨n, m, edgeBase, maxsize⟩) =
      ⟨⟨n, m, edgeBase, maxsize, csr.offBase, csr.adjBase, bufBase⟩,
        ⟨pool.1, pool.2, 0, 0, 0, partRankThreshold⟩⟩ := by
    rw [partSetup_def]
    rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_bind,
      clientResult_bind_allocDirty, StateTransitionSpec.clientResult_bind,
      StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_pure]
  have hs'_eq : (Memory.spec 0).clientState s (partSetup ⟨n, m, edgeBase, maxsize⟩) = s5 := by
    rw [partSetup_def]
    rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
      clientState_bind_allocDirty, StateTransitionSpec.clientState_bind,
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_pure]
  have hs5_below_buf : ∀ a < bufBase, s5.mem a = s2.mem a := fun a ha => by
    have hz2 : a ∉ Set.Ico (bufBase + 14 * n) (bufBase + 14 * n + m) := by
      simp only [Set.mem_Ico]; omega
    have hz1 : a ∉ Set.Ico bufBase (bufBase + 2 * n) := by
      simp only [Set.mem_Ico]; omega
    exact (hagree_z2 a hz2).trans (hagree_z1 a hz1)
  have hs5_below_init : ∀ a < s.frontier, s5.mem a = s.mem a := fun a ha => by
    have ha1 : a < s1.frontier := by rw [hfr1]; omega
    have ha2 : a < bufBase := by dsimp only [bufBase]; rw [hfr2]; omega
    exact (hs5_below_buf a ha2).trans ((hmod2 a ha1).trans (hmod_csr.2 a ha (Set.notMem_empty a)))
  have hin' : HoldsIndexedEdges edgeBase es s5.mem :=
    hin.congr fun a _ ha => hs5_below_init a (by omega)
  have hcsr' : HoldsUndirCSR csr.offBase csr.adjBase es s5.mem :=
    hcsr_hold.congr
      (fun a ha1 ha2 => by
        have ha_s1 : a < s1.frontier := by rw [hcsr1] at ha1 ha2; rw [hfr1]; omega
        have hb : a < bufBase := by dsimp only [bufBase]; rw [hfr2]; omega
        exact (hs5_below_buf a hb).trans (hmod2 a ha_s1))
      (fun a ha1 ha2 => by
        have ha_s1 : a < s1.frontier := by rw [hcsr2] at ha1 ha2; rw [hfr1]; omega
        have hb : a < bufBase := by dsimp only [bufBase]; rw [hfr2]; omega
        exact (hs5_below_buf a hb).trans (hmod2 a ha_s1))
  have hsh' : SHInv w 0 0 (2 * m) (4 * m) ⟨pool.1, pool.2, 0, 0, 0, partRankThreshold⟩
      [] (fun _ => 0) s5 :=
    shInit_inv h16 hwf5 (by omega) (by omega)
      (by rw [hp1, hfr5, hfr4]; dsimp only [s3, bufBase]; rw [hfr2]; omega)
      (by rw [hp2, hfr5, hfr4]; dsimp only [s3, bufBase]; rw [hfr2]; omega)
      (by rw [hp1, hp2]; exact Or.inl (by omega))
      (by dsimp only [shFuelBound, partRankThreshold]; exact hfit.of_le (by omega))
  have hedges_in : ∀ j < m, s.mem (edgeBase + 4 * j) < n ∧ s.mem (edgeBase + 4 * j + 1) < n :=
    fun j hj => ⟨(hin j hj).1 ▸ es[j].u.isLt, (hin j hj).2.1 ▸ es[j].v.isLt⟩
  have hsafe : partSetupSafe w ⟨n, m, edgeBase, maxsize⟩ s := by
    rw [partSetupSafe_def]
    exact ⟨h16, hin_lt, hfit_csr, hedges_in, hfit_pool, hfit_buf, h2n, hm⟩
  have hval4' : ∀ j < 2 * n, s5.mem (bufBase + j) = 0 := fun j hj => by
    have hz2 : bufBase + j ∉ Set.Ico (bufBase + 14 * n) (bufBase + 14 * n + m) := by
      simp only [Set.mem_Ico]; omega
    exact (hagree_z2 _ hz2).trans (hval4 j hj)
  let L : PartLayout w n :=
    { es := es, edgeBase := edgeBase, maxsize := maxsize, offBase := csr.offBase,
      adjBase := csr.adjBase, itemBase := pool.1, nodeBase := pool.2, bufBase := bufBase,
      initFrontier := s.frontier, h16 := h16, hmax_pos := hmax_pos, hn_pos := hn_pos,
      hin_lt := hin_lt, hoff_ge := le_of_eq hcsr1.symm,
      hoff_adj := by rw [hcsr1, hcsr2]; omega,
      hadj_it := by rw [hcsr2, hp1, hfr1]; omega,
      hit_nd := by rw [hp1, hp2],
      hnd_buf := by dsimp only [bufBase]; rw [hp2, hfr2],
      hfit_end := by dsimp only [bufBase]; rw [hfr2, hfr1]; exact hfit.of_le (by omega),
      hfit_fuel := hfit.of_le (by dsimp only [partSHFuel, shFuelBound, partRankThreshold]; omega) }
  refine ⟨hsafe, hv_all, hcost_all, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    L, ?_⟩
  · rw [hres_eq]
  · rw [hres_eq]
  · rw [hres_eq]
  · rw [hres_eq]
  · rw [hres_eq]; dsimp only [bufBase]; rw [hfr2, hfr1]; dsimp only [m]; omega
  · rw [hres_eq]
  · rw [hs'_eq, hres_eq, hfr5, hfr4]
  · rw [hs'_eq]; exact hwf5
  · intro a ha; rw [hs'_eq]; exact hs5_below_init a ha
  · rw [hs'_eq]; exact hin'
  · rw [hs'_eq, hres_eq]; exact hcsr'
  · rw [hs'_eq, hres_eq]; exact hsh'
  · rw [hs'_eq, hres_eq]; exact hval4'
  · rw [hs'_eq, hres_eq]; exact hval5
  · rw [hres_eq]; refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Dynamic Soft-Heap Vertex Expansion (`partTryInsertEdge`, `partExpandVertex`) -/

private theorem partTryInsertEdge_bind_eq {d : PartTryInsertArgs} {s : Memory.State}
    (hst : s.mem (d.bufBase + 14 * d.n + d.eIdx) = 0)
    (hnb : s.mem (d.bufBase + d.n + d.nb) ≠ d.cid) :
    let wt := s.mem (d.edgeBase + 4 * d.eIdx + 2)
    (Memory.spec 0).clientResult s (partTryInsertEdge d) =
      (Memory.spec 0).clientResult s (shInsert (d.sh, d.eIdx, wt, 500 * (2 * d.m + 1))) ∧
    (Memory.spec 0).clientState s (partTryInsertEdge d) =
      (Memory.spec 0).clientState s (shInsert (d.sh, d.eIdx, wt, 500 * (2 * d.m + 1))) ∧
    memoryCost (partTryInsertEdge d) s =
      3 + memoryCost (shInsert (d.sh, d.eIdx, wt, 500 * (2 * d.m + 1))) s := by
  rw [partTryInsertEdge_def]
  refine ⟨?_, ?_, ?_⟩
  · rw [clientResult_bind_read, ite_eq_left hst, clientResult_bind_read, ite_eq_left hnb,
      clientResult_bind_read]
  · rw [clientState_bind_read, ite_eq_left hst, clientState_bind_read, ite_eq_left hnb,
      clientState_bind_read]
  · rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read, ite_eq_left hst,
      memoryCost_bind', memoryCost_read, clientResult_read, clientState_read, ite_eq_left hnb,
      memoryCost_bind', memoryCost_read, clientResult_read, clientState_read]; omega

private theorem partTryInsertEdge_noop {w : ℕ} {d : PartTryInsertArgs} {s : Memory.State}
    (h16 : Fits w 16) (hfuel : Fits w (500 * (2 * d.m + 1)))
    (hbuf : Fits w (d.bufBase + 14 * d.n + 14 * d.m))
    (hst_lt : d.bufBase + 14 * d.n + d.eIdx < s.frontier)
    (hnb_imp : s.mem (d.bufBase + 14 * d.n + d.eIdx) = 0 →
      d.bufBase + d.n + d.nb < s.frontier ∧ s.mem (d.bufBase + d.n + d.nb) = d.cid) :
    partTryInsertEdgeSafe w d s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (partTryInsertEdge d)) ∧
    (Memory.spec 0).clientResult s (partTryInsertEdge d) = d.sh ∧
    (Memory.spec 0).clientState s (partTryInsertEdge d) = s ∧
    memoryCost (partTryInsertEdge d) s ≤ 2 := by
  rw [partTryInsertEdgeSafe_def, partTryInsertEdge_def]
  by_cases hst : s.mem (d.bufBase + 14 * d.n + d.eIdx) = 0
  · obtain ⟨hnb_fr, hnb_eq⟩ := hnb_imp hst
    have hnb : ¬(s.mem (d.bufBase + d.n + d.nb) ≠ d.cid) := not_not.mpr hnb_eq
    refine ⟨⟨h16, hfuel, hbuf, hst_lt, fun _ => ⟨hnb_fr, fun hne => absurd hnb_eq hne⟩⟩,
      ?_, ?_, ?_, ?_⟩
    · refine validHistory_read_bind hst_lt ?_; rw [ite_eq_left hst]
      refine validHistory_read_bind hnb_fr ?_; rw [ite_eq_right hnb]
      exact validHistory_pure w _ _
    · rw [clientResult_bind_read, ite_eq_left hst, clientResult_bind_read, ite_eq_right hnb]
      exact StateTransitionSpec.clientResult_pure _ _
    · rw [clientState_bind_read, ite_eq_left hst, clientState_bind_read, ite_eq_right hnb]
      exact StateTransitionSpec.clientState_pure _ _
    · rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
        ite_eq_left hst, memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
        ite_eq_right hnb, memoryCost_pure]
  · refine ⟨⟨h16, hfuel, hbuf, hst_lt, fun h0 => absurd h0 hst⟩, ?_, ?_, ?_, ?_⟩
    · refine validHistory_read_bind hst_lt ?_; rw [ite_eq_right hst]
      exact validHistory_pure w _ _
    · rw [clientResult_bind_read, ite_eq_right hst]
      exact StateTransitionSpec.clientResult_pure _ _
    · rw [clientState_bind_read, ite_eq_right hst]; exact StateTransitionSpec.clientState_pure _ _
    · rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
        ite_eq_right hst, memoryCost_pure]; omega

/-- Specification of `partTryInsertEdge`: conditionally inserts an active cross edge into the
Soft Heap with amortized slack `≤ 2445` (`3` reads + `2440` at `rankThreshold = 8`). -/
theorem partTryInsertEdge_spec {w n : ℕ} (L : PartLayout w n)
    (cid nb eIdx ic₀ nc₀ : ℕ) (h : SHHandle) (roots : List SHTree) (created : ℕ → ℕ)
    (s : Memory.State) (hfr : s.frontier = L.bufBase + (14 * n + 14 * L.es.length))
    (hrt : h.rankThreshold = partRankThreshold)
    (hsh : SHInv w ic₀ nc₀ (2 * L.es.length) (4 * L.es.length) h roots created s)
    (hin_edges : HoldsIndexedEdges L.edgeBase L.es s.mem)
    (he_lt : eIdx < L.es.length) (hnb_lt : nb < n)
    (hcap : h.itemCount < 2 * L.es.length ∨
      s.mem (L.bufBase + 14 * n + eIdx) ≠ 0 ∨ s.mem (L.bufBase + n + nb) = cid) :
    let d : PartTryInsertArgs := ⟨L.edgeBase, L.bufBase, n, L.es.length, cid, nb, eIdx, h⟩
    let prog := partTryInsertEdge d
    let h' := (Memory.spec 0).clientResult s prog
    let s' := (Memory.spec 0).clientState s prog
    partTryInsertEdgeSafe w d s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    s'.frontier = s.frontier ∧
    Memory.WellFormed w s' ∧
    (∀ a, s'.mem a ≠ s.mem a → InSHPool ic₀ nc₀ (2 * L.es.length) (4 * L.es.length) h a) ∧
    h'.itemBase = h.itemBase ∧ h'.nodeBase = h.nodeBase ∧
    h'.rankThreshold = partRankThreshold ∧
    ∃ roots' created',
      SHInv w ic₀ nc₀ (2 * L.es.length) (4 * L.es.length) h' roots' created' s' ∧
      (memoryCost prog s : ℚ) + totalPhi partRankThreshold roots' ≤
        totalPhi partRankThreshold roots + 2445 ∧
      (∀ p ∈ forestEntries roots',
        (∃ c₀, (p.1, c₀) ∈ forestEntries roots ∧ c₀ ≤ p.2) ∨
        (s.mem (L.bufBase + 14 * n + eIdx) = 0 ∧ s.mem (L.bufBase + n + nb) ≠ cid ∧
          p.1 = ⟨h.itemCount + 1, eIdx, L.es[eIdx].weight⟩ ∧ L.es[eIdx].weight ≤ p.2)) ∧
      (s.mem (L.bufBase + 14 * n + eIdx) = 0 → s.mem (L.bufBase + n + nb) ≠ cid →
        h'.itemCount = h.itemCount + 1 ∧
        (forestItems roots').Perm
          (⟨h.itemCount + 1, eIdx, L.es[eIdx].weight⟩ :: forestItems roots)) ∧
      (¬(s.mem (L.bufBase + 14 * n + eIdx) = 0 ∧ s.mem (L.bufBase + n + nb) ≠ cid) →
        h' = h ∧ s' = s ∧ roots' = roots ∧ created' = created) := by
  let m := L.es.length
  let d : PartTryInsertArgs := ⟨L.edgeBase, L.bufBase, n, m, cid, nb, eIdx, h⟩
  have h16 := L.h16
  have hwf := hsh.wf
  have hfuel_fit : Fits w (500 * (2 * m + 1)) := by
    simpa [partSHFuel, shFuelBound, partRankThreshold] using L.hfit_fuel
  have hbuf_fit : Fits w (L.bufBase + 14 * n + 14 * m) := L.hfit_end.of_le (by omega)
  have hst_lt : L.bufBase + 14 * n + eIdx < s.frontier := by rw [hfr]; omega
  have hnb_fr : L.bufBase + n + nb < s.frontier := by rw [hfr]; omega
  have he_lt_fr : L.edgeBase + 4 * eIdx + 2 < s.frontier := by
    have := L.edge_lt_itemBase; have := L.hit_nd; have := L.hnd_buf; rw [hfr]; omega
  by_cases hcond : s.mem (L.bufBase + 14 * n + eIdx) = 0 ∧ s.mem (L.bufBase + n + nb) ≠ cid
  · obtain ⟨hst, hnb⟩ := hcond
    have hcap_lt : h.itemCount < 2 * m := by
      rcases hcap with hlt | hne | heq
      · exact hlt
      · exact absurd hst hne
      · exact absurd heq hnb
    have he_fit : Fits w eIdx := L.hfit_end.of_le (by omega)
    have hwt_fit : Fits w (s.mem (L.edgeBase + 4 * eIdx + 2)) := hwf.mem_fits _
    have hfuel_ge : shFuelBound h.rankThreshold (2 * m) ≤ 500 * (2 * m + 1) := by
      rw [hrt]; dsimp only [shFuelBound, partRankThreshold]; exact le_rfl
    have hins_all := shInsert_spec hsh hcap_lt he_fit hwt_fit hfuel_ge hfuel_fit
    rcases hins_all with ⟨hv_ins, hsafe_ins, h_ib, h_nb, h_ic, _h_nc, h_rt, h_sfr, h_mod,
      roots', created', hsh', hperm', hent', hpot'⟩
    have hsafe : partTryInsertEdgeSafe w d s := by
      rw [partTryInsertEdgeSafe_def]
      exact ⟨h16, hfuel_fit, hbuf_fit, hst_lt, fun _ => ⟨hnb_fr, fun _ => ⟨he_lt_fr, hsafe_ins⟩⟩⟩
    have hvh : (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (partTryInsertEdge d)) := by
      rw [partTryInsertEdge_def]
      refine validHistory_read_bind hst_lt ?_
      rw [ite_eq_left hst]
      refine validHistory_read_bind hnb_fr ?_
      rw [ite_eq_left hnb]
      exact validHistory_read_bind he_lt_fr hv_ins
    obtain ⟨hres_eq, hs'_eq, hcost_eq⟩ := partTryInsertEdge_bind_eq (d := d) hst hnb
    dsimp only [d] at hres_eq hs'_eq hcost_eq ⊢
    have hwt_eq : s.mem (L.edgeBase + 4 * eIdx + 2) = L.es[eIdx].weight :=
      (hin_edges eIdx he_lt).2.2.1
    have hrt' : ((Memory.spec 0).clientResult s (partTryInsertEdge d)).rankThreshold =
        partRankThreshold := by rw [hres_eq, h_rt, hrt]
    refine ⟨hsafe, hvh, by rw [hs'_eq, h_sfr], by rw [hs'_eq]; exact hsh'.wf,
      by rw [hs'_eq]; exact h_mod,
      by rw [hres_eq, h_ib], by rw [hres_eq, h_nb], hrt', roots', created',
      by rw [hres_eq, hs'_eq]; exact hsh', ?_, ?_, ?_, fun hnot => absurd ⟨hst, hnb⟩ hnot⟩
    · have hpot_q : (memoryCost (shInsert (h, eIdx, s.mem (L.edgeBase + 4 * eIdx + 2),
          500 * (2 * m + 1))) s : ℚ) + totalPhi partRankThreshold roots' ≤
          totalPhi partRankThreshold roots + 2440 := by
        rw [hrt] at hpot'
        have : (240 * ((partRankThreshold : ℕ) : ℚ) + 520 : ℚ) = 2440 := by
          norm_num [partRankThreshold]
        linarith
      rw [hcost_eq, Nat.cast_add]; push_cast; linarith
    · intro p hp
      rcases hent' p hp with ⟨hp1, hp2⟩ | hc₀
      · exact .inr ⟨hst, hnb, hp1.trans (by rw [hwt_eq]), hwt_eq ▸ hp2⟩
      · exact .inl hc₀
    · intro _ _
      refine ⟨by rw [hres_eq, h_ic], ?_⟩
      rw [hwt_eq] at hperm'; exact hperm'
  · have hnb_imp : s.mem (L.bufBase + 14 * n + eIdx) = 0 →
        L.bufBase + n + nb < s.frontier ∧ s.mem (L.bufBase + n + nb) = cid :=
      fun h0 => ⟨hnb_fr, not_not.mp fun hne => hcond ⟨h0, hne⟩⟩
    obtain ⟨hsafe, hvh, hres_eq, hs'_eq, hcost_le⟩ := partTryInsertEdge_noop (d := d)
      h16 hfuel_fit hbuf_fit hst_lt hnb_imp
    refine ⟨hsafe, hvh, by rw [hs'_eq], by rw [hs'_eq]; exact hwf,
      fun a hne => by rw [hs'_eq] at hne; exact absurd rfl hne,
      by rw [hres_eq], by rw [hres_eq], by rw [hres_eq, hrt], roots, created,
      by rw [hres_eq, hs'_eq]; exact hsh, ?_, fun p hp => .inl ⟨p.2, hp, le_rfl⟩,
      fun h0 hne => absurd ⟨h0, hne⟩ hcond, fun _ => ⟨hres_eq, hs'_eq, rfl, rfl⟩⟩
    have hc : (memoryCost (partTryInsertEdge d) s : ℚ) ≤ 2 := by exact_mod_cast hcost_le
    linarith

/-- Edge IDs appearing in a CSR adjacency slice of a loopless multigraph (`u ≠ v`) have no
duplicates. -/
private theorem csr_slice_edgeIds_nodup {n offBase adjBase : ℕ} {es : List (IndexedEdge n)}
    {mem : ℕ → ℕ} (hcsr : HoldsUndirCSR offBase adjBase es mem)
    (hsimp : ∀ i : Fin es.length, es[i.val].u ≠ es[i.val].v) (u : Fin n) :
    ((List.range (mem (offBase + u.val + 1) - mem (offBase + u.val))).map (fun k =>
      let p := mem (offBase + u.val) + k
      mem (adjBase + 2 * p + 1))).Nodup := by
  have hperm := (hcsr.adj_perm u).map Prod.snd
  rw [List.map_map] at hperm
  have hmap_eq :
      (List.range (mem (offBase + u.val + 1) - mem (offBase + u.val))).map
        (Prod.snd ∘ fun k =>
          let p := mem (offBase + u.val) + k
          (mem (adjBase + 2 * p), mem (adjBase + 2 * p + 1))) =
      (List.range (mem (offBase + u.val + 1) - mem (offBase + u.val))).map (fun k =>
        let p := mem (offBase + u.val) + k
        mem (adjBase + 2 * p + 1)) := rfl
  rw [hmap_eq] at hperm
  rw [hperm.nodup_iff, List.map_append, List.map_map, List.map_map]
  have hnd1 : (((List.finRange es.length).filter (fun i => decide (es[i.val].u = u))).map
      (Prod.snd ∘ fun i => (es[i.val].v.val, i.val))).Nodup := by
    change (((List.finRange es.length).filter
      (fun i => decide (es[i.val].u = u))).map Fin.val).Nodup
    exact ((List.nodup_finRange _).filter _).map Fin.val_injective
  have hnd2 : (((List.finRange es.length).filter (fun i => decide (es[i.val].v = u))).map
      (Prod.snd ∘ fun i => (es[i.val].u.val, i.val))).Nodup := by
    change (((List.finRange es.length).filter
      (fun i => decide (es[i.val].v = u))).map Fin.val).Nodup
    exact ((List.nodup_finRange _).filter _).map Fin.val_injective
  refine List.nodup_append.mpr ⟨hnd1, hnd2, ?_⟩
  intro x hx1 y hy hxy
  subst hxy
  obtain ⟨i, hi_f, hi_eq⟩ := List.mem_map.mp hx1
  obtain ⟨j, hj_f, hj_eq⟩ := List.mem_map.mp hy
  have hi_u : es[i.val].u = u := of_decide_eq_true (List.mem_filter.mp hi_f).2
  have hj_v : es[j.val].v = u := of_decide_eq_true (List.mem_filter.mp hj_f).2
  have heq : i = j := Fin.ext (hi_eq.trans hj_eq.symm)
  rw [heq] at hi_u
  exact hsimp j (hi_u.trans hj_v.symm)

private structure ExpandIterWitness {w n : ℕ} (L : PartLayout w n)
    (cid ic₀ nc₀ : ℕ) (u : Fin n) (h₀ hInit : SHHandle) (roots₀ rootsInit : List SHTree)
    (s₀ : Memory.State) (edgeState0 : ℕ → ℕ) (j₀ k : ℕ)
    (st : PartExpandState) (s : Memory.State) where
  roots : List SHTree
  created : ℕ → ℕ
  hidx : st.idx = j₀ + k
  hfr : s.frontier = s₀.frontier
  hmod : ∀ x, s.mem x ≠ s₀.mem x →
    InSHPool ic₀ nc₀ (2 * L.es.length) (4 * L.es.length) h₀ x
  hib : st.sh.itemBase = h₀.itemBase
  hnb : st.sh.nodeBase = h₀.nodeBase
  hrt : st.sh.rankThreshold = partRankThreshold
  hic_ge : hInit.itemCount ≤ st.sh.itemCount
  hic_le : st.sh.itemCount ≤ hInit.itemCount + k
  hsh : SHInv w ic₀ nc₀ (2 * L.es.length) (4 * L.es.length) st.sh roots created s
  hok : ∀ p ∈ forestEntries roots, p.1.origKey ≤ p.2
  hnd : ((forestItems roots).map SHItem.val).Nodup
  hlen : (forestItems roots).length =
    (forestItems rootsInit).length + (st.sh.itemCount - hInit.itemCount)
  hkeep : ∀ it ∈ forestItems rootsInit, it ∈ forestItems roots
  hprev : ∀ p ∈ forestEntries roots,
    p.1.val ∈ (forestItems roots₀).map SHItem.val ∨
    ∃ t, s₀.mem (L.offBase + u.val) ≤ t ∧ t < j₀ + k ∧
      s₀.mem (L.adjBase + 2 * t + 1) = p.1.val
  hent : ∀ p ∈ forestEntries roots,
    (∃ c₀, (p.1, c₀) ∈ forestEntries rootsInit ∧ c₀ ≤ p.2) ∨
    ∃ t : ℕ, j₀ ≤ t ∧ t < j₀ + k ∧
      ∃ eIdx : Fin L.es.length, s₀.mem (L.adjBase + 2 * t) < n ∧
        s₀.mem (L.adjBase + 2 * t + 1) = eIdx.val ∧
        p.1.val = eIdx.val ∧ p.1.origKey = L.es[eIdx].weight ∧ p.1.origKey ≤ p.2 ∧
        edgeState0 eIdx.val = 0 ∧
        s₀.mem (L.bufBase + n + s₀.mem (L.adjBase + 2 * t)) ≠ cid
  hcov : ∀ t : ℕ, j₀ ≤ t → t < j₀ + k →
    let nb := s₀.mem (L.adjBase + 2 * t)
    let eIdx := s₀.mem (L.adjBase + 2 * t + 1)
    edgeState0 eIdx = 0 → s₀.mem (L.bufBase + n + nb) ≠ cid →
    ∃ p ∈ forestEntries roots,
      p.1.val = eIdx ∧ ∃ hlt : eIdx < L.es.length,
        p.1.origKey = (L.es[eIdx]'hlt).weight ∧ p.1.origKey ≤ p.2

/-- Loop invariant and amortized `2450`-per-half-edge specification for iterating
`partExpandStep` across `k` adjacent half-edges of `u`. -/
theorem partExpandVertex_iter_spec {w n : ℕ} (L : PartLayout w n)
    (cid ic₀ nc₀ : ℕ) (u : Fin n) (h₀ : SHHandle) (roots₀ : List SHTree)
    (s₀ : Memory.State) (edgeState0 : ℕ → ℕ)
    (hfr₀ : s₀.frontier = L.bufBase + (14 * n + 14 * L.es.length))
    (hib₀ : h₀.itemBase = L.itemBase) (hnb₀ : h₀.nodeBase = L.nodeBase)
    (hcsr₀ : HoldsUndirCSR L.offBase L.adjBase L.es s₀.mem)
    (hin₀ : HoldsIndexedEdges L.edgeBase L.es s₀.mem)
    (hedgeSt₀ : ∀ i < L.es.length, s₀.mem (L.bufBase + 14 * n + i) = edgeState0 i)
    (hsimp : ∀ e : Fin L.es.length, (L.es[e.val]'e.isLt).u ≠ (L.es[e.val]'e.isLt).v)
    (hno_dup₀ : ∀ p ∈ forestEntries roots₀,
      ∃ eIdx : Fin L.es.length, p.1.val = eIdx.val ∧
        ((L.es[eIdx.val]'eIdx.isLt).u = u ∨ (L.es[eIdx.val]'eIdx.isLt).v = u →
          ∃ nb : Fin n, (((L.es[eIdx.val]'eIdx.isLt).u = u ∧ (L.es[eIdx.val]'eIdx.isLt).v = nb) ∨
            ((L.es[eIdx.val]'eIdx.isLt).v = u ∧ (L.es[eIdx.val]'eIdx.isLt).u = nb)) ∧
            s₀.mem (L.bufBase + n + nb.val) = cid))
    (k j₀ : ℕ) (hInit : SHHandle) (rootsInit : List SHTree) (createdInit : ℕ → ℕ)
    (sInit : Memory.State)
    (hjk : j₀ + k ≤ s₀.mem (L.offBase + u.val + 1))
    (hj_ge : s₀.mem (L.offBase + u.val) ≤ j₀)
    (hfr : sInit.frontier = s₀.frontier)
    (hmod : ∀ x, sInit.mem x ≠ s₀.mem x →
      InSHPool ic₀ nc₀ (2 * L.es.length) (4 * L.es.length) h₀ x)
    (hib : hInit.itemBase = h₀.itemBase) (hnb : hInit.nodeBase = h₀.nodeBase)
    (hrtInit : hInit.rankThreshold = partRankThreshold)
    (hsh : SHInv w ic₀ nc₀ (2 * L.es.length) (4 * L.es.length) hInit rootsInit createdInit sInit)
    (hok : ∀ p ∈ forestEntries rootsInit, p.1.origKey ≤ p.2)
    (hnd : ((forestItems rootsInit).map SHItem.val).Nodup)
    (hprev : ∀ p ∈ forestEntries rootsInit,
      p.1.val ∈ (forestItems roots₀).map SHItem.val ∨
      ∃ t, s₀.mem (L.offBase + u.val) ≤ t ∧ t < j₀ ∧
        s₀.mem (L.adjBase + 2 * t + 1) = p.1.val)
    (hcap_j : hInit.itemCount + (s₀.mem (L.offBase + u.val + 1) - j₀) ≤ 2 * L.es.length) :
    let m := L.es.length
    let stepD : PartAdjEnv := ⟨L.adjBase, L.edgeBase, L.bufBase, n, m, cid⟩
    let prog := iterate partExpandStep stepD k ⟨j₀, hInit⟩
    let a' := (Memory.spec 0).clientResult sInit prog
    let s' := (Memory.spec 0).clientState sInit prog
    iterationSafe partExpandStep partExpandStepSafe w stepD k ⟨j₀, hInit⟩ sInit ∧
    (Memory.spec w).ValidHistory sInit ((Memory.spec w).clientHistory sInit prog) ∧
    a'.idx = j₀ + k ∧ s'.frontier = s₀.frontier ∧
    (∀ x, s'.mem x ≠ s₀.mem x → InSHPool ic₀ nc₀ (2 * m) (4 * m) h₀ x) ∧
    a'.sh.itemBase = h₀.itemBase ∧ a'.sh.nodeBase = h₀.nodeBase ∧
    a'.sh.rankThreshold = partRankThreshold ∧
    hInit.itemCount ≤ a'.sh.itemCount ∧ a'.sh.itemCount ≤ hInit.itemCount + k ∧
    ∃ roots' created',
      SHInv w ic₀ nc₀ (2 * m) (4 * m) a'.sh roots' created' s' ∧
      (memoryCost prog sInit : ℚ) + totalPhi partRankThreshold roots' ≤
        totalPhi partRankThreshold rootsInit + 2450 * k ∧
      (forestItems roots').length =
        (forestItems rootsInit).length + (a'.sh.itemCount - hInit.itemCount) ∧
      ((forestItems roots').map SHItem.val).Nodup ∧
      (∀ it ∈ forestItems rootsInit, it ∈ forestItems roots') ∧
      (∀ p ∈ forestEntries roots',
        (∃ c₀, (p.1, c₀) ∈ forestEntries rootsInit ∧ c₀ ≤ p.2) ∨
        ∃ t : ℕ, j₀ ≤ t ∧ t < j₀ + k ∧
          ∃ eIdx : Fin m, s₀.mem (L.adjBase + 2 * t) < n ∧
            s₀.mem (L.adjBase + 2 * t + 1) = eIdx.val ∧
            p.1.val = eIdx.val ∧ p.1.origKey = L.es[eIdx].weight ∧ p.1.origKey ≤ p.2 ∧
            edgeState0 eIdx.val = 0 ∧
            s₀.mem (L.bufBase + n + s₀.mem (L.adjBase + 2 * t)) ≠ cid) ∧
      (∀ t : ℕ, j₀ ≤ t → t < j₀ + k →
        let nb := s₀.mem (L.adjBase + 2 * t)
        let eIdx := s₀.mem (L.adjBase + 2 * t + 1)
        edgeState0 eIdx = 0 → s₀.mem (L.bufBase + n + nb) ≠ cid →
        ∃ p ∈ forestEntries roots',
          p.1.val = eIdx ∧ ∃ hlt : eIdx < m,
            p.1.origKey = (L.es[eIdx]'hlt).weight ∧ p.1.origKey ≤ p.2) := by
  let m := L.es.length
  let startJ := s₀.mem (L.offBase + u.val)
  let endJ := s₀.mem (L.offBase + u.val + 1)
  have hend_le : endJ ≤ 2 * m := by
    simpa [endJ, Nat.add_assoc] using hcsr₀.offset_le_end (u.val + 1) u.isLt
  have hslice_nd := csr_slice_edgeIds_nodup hcsr₀ hsimp u
  let stepD : PartAdjEnv := ⟨L.adjBase, L.edgeBase, L.bufBase, n, m, cid⟩
  let S : Set ℕ := {x | InSHPool ic₀ nc₀ (2 * m) (4 * m) h₀ x}
  let WType := Σ p : PartExpandState × Memory.State × ℕ,
    ExpandIterWitness L cid ic₀ nc₀ u h₀ hInit roots₀ rootsInit s₀ edgeState0 j₀ p.2.2 p.1 p.2.1
  let inv (t : ℕ) (wt : WType) (st : PartExpandState) (s : Memory.State) : Prop :=
    wt.1.1 = st ∧ wt.1.2.1 = s ∧ wt.1.2.2 = t
  let pot (_ : ℕ) (wt : WType) : ℚ := totalPhi partRankThreshold wt.2.roots
  have hstep : ∀ t < k, ∀ wt st s, inv t wt st s →
      partExpandStepSafe w (stepD, st) s ∧
      (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (partExpandStep (stepD, st))) ∧
      let st' := (Memory.spec 0).clientResult s (partExpandStep (stepD, st))
      let s' := (Memory.spec 0).clientState s (partExpandStep (stepD, st))
      ∃ wt' : WType,
        inv (t + 1) wt' st' s' ∧
        (memoryCost (partExpandStep (stepD, st)) s : ℚ) + pot (t + 1) wt' ≤ pot t wt + 2450 ∧
        Memory.Modifies S s s' := by
    rintro t₀ ht_lt ⟨⟨st', s', t⟩, W⟩ st s ⟨hst_eq, hs_eq, ht_eq⟩
    subst hst_eq hs_eq
    change ExpandIterWitness L cid ic₀ nc₀ u h₀ hInit roots₀ rootsInit s₀ edgeState0 j₀ t st' s'
      at W
    have ht_eq' : t = t₀ := ht_eq
    have ht_lt : t < k := ht_eq' ▸ ht_lt
    let j := j₀ + t
    have hidx_eq : st'.idx = j := W.hidx
    have hj_lt_end : j < endJ := by dsimp only [j, endJ]; omega
    have hj_ge' : startJ ≤ j := by dsimp only [j, startJ]; omega
    have hagree := L.agree_outside_inSHPool hib₀ hnb₀ W.hmod
    have hin_s : HoldsIndexedEdges L.edgeBase L.es s'.mem :=
      (L.congr_below_itemBase hagree.1).1 hin₀
    have hpair_mem : (s₀.mem (L.adjBase + 2 * j), s₀.mem (L.adjBase + 2 * j + 1)) ∈
        (List.range (endJ - startJ)).map (fun q =>
          let p := startJ + q
          (s₀.mem (L.adjBase + 2 * p), s₀.mem (L.adjBase + 2 * p + 1))) := by
      refine List.mem_map.mpr ⟨j - startJ, List.mem_range.mpr (by omega), ?_⟩
      dsimp only; rw [show startJ + (j - startJ) = j by omega]
    rw [hcsr₀.mem_slice_iff] at hpair_mem
    rcases hpair_mem with ⟨eFin, heFin_id, heFin_ends⟩
    have he_lt : s₀.mem (L.adjBase + 2 * j + 1) < m := heFin_id ▸ eFin.isLt
    have hnb_lt : s₀.mem (L.adjBase + 2 * j) < n := by
      rcases heFin_ends with ⟨_, hv⟩ | ⟨_, hu⟩
      · exact hv ▸ L.es[eFin].v.isLt
      · exact hu ▸ L.es[eFin].u.isLt
    have hadj_lt_j : L.adjBase + 2 * j + 1 < s'.frontier := by
      have := L.hadj_it; have := L.hit_nd; have := L.hnd_buf
      rw [W.hfr, hfr₀]; omega
    have hj1_fit : Fits w (st'.idx + 1) := L.hfit_end.of_le (by rw [hidx_eq]; omega)
    have hadj0_eq : s'.mem (L.adjBase + 2 * st'.idx) = s₀.mem (L.adjBase + 2 * j) := by
      rw [hidx_eq]; exact hagree.1 _ (by have := L.hadj_it; omega)
    have hadj1_eq : s'.mem (L.adjBase + 2 * st'.idx + 1) = s₀.mem (L.adjBase + 2 * j + 1) := by
      rw [hidx_eq]; exact hagree.1 _ (by have := L.hadj_it; omega)
    have hcap_step : st'.sh.itemCount < 2 * m := by
      have := W.hic_le; dsimp only [endJ] at *; omega
    have htry := partTryInsertEdge_spec L cid (s₀.mem (L.adjBase + 2 * j))
      (s₀.mem (L.adjBase + 2 * j + 1)) ic₀ nc₀ st'.sh W.roots W.created s'
      (W.hfr.trans hfr₀) W.hrt W.hsh hin_s he_lt hnb_lt (Or.inl hcap_step)
    rcases htry with ⟨htry_safe, htry_vh, htry_fr, _htry_wf, htry_mod, htry_ib, htry_nb,
      htry_rt, roots₁, created₁, hsh₁, htry_cost, htry_ent, htry_ic, htry_nc⟩
    have htry_safe' : partTryInsertEdgeSafe w ⟨L.edgeBase, L.bufBase, n, m, cid,
        s'.mem (L.adjBase + 2 * st'.idx), s'.mem (L.adjBase + 2 * st'.idx + 1), st'.sh⟩ s' := by
      simpa only [hadj0_eq, hadj1_eq] using htry_safe
    have hstep_safe : partExpandStepSafe w (stepD, st') s' := by
      rw [partExpandStepSafe_def]
      exact ⟨L.h16, hj1_fit, by rw [hidx_eq]; exact hadj_lt_j, htry_safe'⟩
    have hstep_vh : (Memory.spec w).ValidHistory s'
        ((Memory.spec w).clientHistory s' (partExpandStep (stepD, st'))) := by
      rw [partExpandStep_def]; dsimp only [stepD, m]
      refine validHistory_read_bind (by rw [hidx_eq]; omega)
        (validHistory_read_bind (by rw [hidx_eq]; exact hadj_lt_j) ?_)
      exact validHistory_bind_step
        (by simpa only [hadj0_eq, hadj1_eq] using htry_vh) (validHistory_pure w _ _)
    let tryD : PartTryInsertArgs := ⟨L.edgeBase, L.bufBase, n, L.es.length, cid,
      s₀.mem (L.adjBase + 2 * j), s₀.mem (L.adjBase + 2 * j + 1), st'.sh⟩
    have hres_eq : (Memory.spec 0).clientResult s' (partExpandStep (stepD, st')) =
        ⟨st'.idx + 1, (Memory.spec 0).clientResult s' (partTryInsertEdge tryD)⟩ := by
      rw [partExpandStep_def]; dsimp only [stepD, tryD, m]
      rw [clientResult_bind_read, clientResult_bind_read, hadj0_eq, hadj1_eq,
        StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_pure]
    have hs'_eq : (Memory.spec 0).clientState s' (partExpandStep (stepD, st')) =
        (Memory.spec 0).clientState s' (partTryInsertEdge tryD) := by
      rw [partExpandStep_def]; dsimp only [stepD, tryD, m]
      rw [clientState_bind_read, clientState_bind_read, hadj0_eq, hadj1_eq,
        StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_pure]
    have hcost_eq : memoryCost (partExpandStep (stepD, st')) s' =
        2 + memoryCost (partTryInsertEdge tryD) s' := by
      rw [partExpandStep_def]; dsimp only [stepD, tryD, m]
      rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
        memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
        hadj0_eq, hadj1_eq, memoryCost_bind', memoryCost_pure, add_zero]
      omega
    have hpool_eq : ∀ x, InSHPool ic₀ nc₀ (2 * m) (4 * m) st'.sh x ↔
        InSHPool ic₀ nc₀ (2 * m) (4 * m) h₀ x := fun x => by
      simp only [InSHPool]; rw [W.hib, W.hnb]
    have hmod_next : ∀ x, ((Memory.spec 0).clientState s' (partTryInsertEdge tryD)).mem x ≠
        s₀.mem x → InSHPool ic₀ nc₀ (2 * m) (4 * m) h₀ x := fun x hx => by
      by_cases hx1 : ((Memory.spec 0).clientState s' (partTryInsertEdge tryD)).mem x = s'.mem x
      · exact W.hmod x (hx1 ▸ hx)
      · exact (hpool_eq x).mp (htry_mod x hx1)
    have hmod_step : Memory.Modifies S s'
        ((Memory.spec 0).clientState s' (partExpandStep (stepD, st'))) := by
      refine modifies_of_agree_outside S (by rw [hs'_eq, htry_fr]) fun x hxS => ?_
      rw [hs'_eq]
      by_contra hne
      exact hxS ((hpool_eq x).mp (htry_mod x hne))
    have hst_agree : s'.mem (L.bufBase + 14 * n + s₀.mem (L.adjBase + 2 * j + 1)) =
        edgeState0 (s₀.mem (L.adjBase + 2 * j + 1)) :=
      (hagree.2 _ (by omega)).trans (hedgeSt₀ _ he_lt)
    have hin_agree : s'.mem (L.bufBase + n + s₀.mem (L.adjBase + 2 * j)) =
        s₀.mem (L.bufBase + n + s₀.mem (L.adjBase + 2 * j)) :=
      hagree.2 _ (by omega)
    let sh1 := (Memory.spec 0).clientResult s' (partTryInsertEdge tryD)
    let s1 := (Memory.spec 0).clientState s' (partTryInsertEdge tryD)
    have hic_bounds : st'.sh.itemCount ≤ sh1.itemCount ∧ sh1.itemCount ≤ st'.sh.itemCount + 1 := by
      by_cases hcond : s'.mem (L.bufBase + 14 * n + s₀.mem (L.adjBase + 2 * j + 1)) = 0 ∧
          s'.mem (L.bufBase + n + s₀.mem (L.adjBase + 2 * j)) ≠ cid
      · have h_ic := (htry_ic hcond.1 hcond.2).1; dsimp only [sh1, tryD]; omega
      · have h_eq := (htry_nc hcond).1
        dsimp only [sh1, tryD]; rw [h_eq]; exact ⟨le_rfl, Nat.le_succ _⟩
    have hok₁ : ∀ p ∈ forestEntries roots₁, p.1.origKey ≤ p.2 := fun p hp => by
      rcases htry_ent p hp with ⟨c₀, hc₀, hle⟩ | ⟨_, _, hp1, hp2⟩
      · exact (W.hok _ hc₀).trans hle
      · rw [hp1]; exact hp2
    have hnd₁ : ((forestItems roots₁).map SHItem.val).Nodup := by
      by_cases hcond : s'.mem (L.bufBase + 14 * n + s₀.mem (L.adjBase + 2 * j + 1)) = 0 ∧
          s'.mem (L.bufBase + n + s₀.mem (L.adjBase + 2 * j)) ≠ cid
      · have hperm := (htry_ic hcond.1 hcond.2).2
        rw [(hperm.map SHItem.val).nodup_iff, List.map_cons]
        refine List.nodup_cons.mpr ⟨?_, W.hnd⟩
        intro hmem_eid
        rw [List.mem_map] at hmem_eid
        rcases hmem_eid with ⟨it', hit', heid'⟩
        rcases mem_forestItems_iff.mp hit' with ⟨c', hc'⟩
        rcases W.hprev (it', c') hc' with hmem₀ | ⟨t_prev, ht_ge, ht_lt, ht_eq⟩
        · rw [List.mem_map] at hmem₀
          rcases hmem₀ with ⟨it₀, hit₀, heid₀⟩
          rcases mem_forestItems_iff.mp hit₀ with ⟨c₀, hc₀⟩
          rcases hno_dup₀ (it₀, c₀) hc₀ with ⟨e₀, he₀_id, he₀_imp⟩
          have he₀_eq : e₀ = eFin := by
            apply Fin.ext
            calc e₀.val = it₀.val := he₀_id.symm
              _ = it'.val := heid₀
              _ = s₀.mem (L.adjBase + 2 * j + 1) := heid'
              _ = eFin.val := heFin_id.symm
          rw [he₀_eq] at he₀_imp
          have hinc_u : (L.es[eFin.val]'eFin.isLt).u = u ∨ (L.es[eFin.val]'eFin.isLt).v = u := by
            rcases heFin_ends with ⟨hu, _⟩ | ⟨hv, _⟩
            · exact .inl hu
            · exact .inr hv
          rcases he₀_imp hinc_u with ⟨nb', hnb'_ends, hnb'_cid⟩
          have hnb_eq : s₀.mem (L.adjBase + 2 * j) = nb'.val := by
            rcases heFin_ends with ⟨hu1, hv1⟩ | ⟨hv1, hu1⟩
            · rcases hnb'_ends with ⟨_, hv2⟩ | ⟨hv2, _⟩
              · rw [← hv1, hv2]
              · exact absurd (hu1.trans hv2.symm) (hsimp eFin)
            · rcases hnb'_ends with ⟨hu2, _⟩ | ⟨_, hu2⟩
              · exact absurd (hv1.trans hu2.symm) (hsimp eFin).symm
              · rw [← hu1, hu2]
          rw [hin_agree, hnb_eq] at hcond
          exact hcond.2 hnb'_cid
        · have hidx1 : j - startJ <
              ((List.range (endJ - startJ)).map (fun q =>
                let p := startJ + q
                s₀.mem (L.adjBase + 2 * p + 1))).length := by
            rw [List.length_map, List.length_range]
            dsimp only [j, startJ, endJ] at hj_lt_end ⊢; omega
          have hidx2 : t_prev - startJ <
              ((List.range (endJ - startJ)).map (fun q =>
                let p := startJ + q
                s₀.mem (L.adjBase + 2 * p + 1))).length := by
            rw [List.length_map, List.length_range]
            dsimp only [j, startJ, endJ] at hj_lt_end ⊢; omega
          have hget_iff := @List.Nodup.getElem_inj_iff _ _ hslice_nd
            (t_prev - startJ)
            (by
              rw [List.length_map, List.length_range]
              dsimp only [j, startJ, endJ] at hj_lt_end ⊢; omega)
            (j - startJ)
            (by
              rw [List.length_map, List.length_range]
              dsimp only [j, startJ, endJ] at hj_lt_end ⊢; omega)
          have hget_eq :
              ((List.range (endJ - startJ)).map (fun q =>
                let p := startJ + q
                s₀.mem (L.adjBase + 2 * p + 1)))[t_prev - startJ]'(by
                  rw [List.length_map, List.length_range]
                  dsimp only [j, startJ, endJ] at hj_lt_end ⊢; omega) =
              ((List.range (endJ - startJ)).map (fun q =>
                let p := startJ + q
                s₀.mem (L.adjBase + 2 * p + 1)))[j - startJ]'(by
                  rw [List.length_map, List.length_range]
                  dsimp only [j, startJ, endJ] at hj_lt_end ⊢; omega) := by
            simp only [List.getElem_map, List.getElem_range]
            rw [show startJ + (t_prev - startJ) = t_prev by omega,
              show startJ + (j - startJ) = j by dsimp only [j, startJ] at hj_ge' ⊢; omega]
            exact ht_eq.trans heid'
          have hne_idx : t_prev - startJ ≠ j - startJ := by
            dsimp only [j, startJ] at hj_ge' ⊢; omega
          exact hne_idx (hget_iff.mp hget_eq)
      · rw [(htry_nc hcond).2.2.1]; exact W.hnd
    have hlen₁ : (forestItems roots₁).length =
        (forestItems rootsInit).length + (sh1.itemCount - hInit.itemCount) := by
      by_cases hcond : s'.mem (L.bufBase + 14 * n + s₀.mem (L.adjBase + 2 * j + 1)) = 0 ∧
          s'.mem (L.bufBase + n + s₀.mem (L.adjBase + 2 * j)) ≠ cid
      · have hic_eq := (htry_ic hcond.1 hcond.2).1
        have hperm := (htry_ic hcond.1 hcond.2).2
        have hl := hperm.length_eq
        rw [List.length_cons, W.hlen] at hl
        have := W.hic_ge; dsimp only [sh1, tryD]; omega
      · rcases htry_nc hcond with ⟨hr1, _, hr2, _⟩
        dsimp only [sh1, tryD]
        rw [hr1, hr2, W.hlen]
    have hkeep_step : ∀ it ∈ forestItems W.roots, it ∈ forestItems roots₁ := fun it hit => by
      by_cases hcond : s'.mem (L.bufBase + 14 * n + s₀.mem (L.adjBase + 2 * j + 1)) = 0 ∧
          s'.mem (L.bufBase + n + s₀.mem (L.adjBase + 2 * j)) ≠ cid
      · exact ((htry_ic hcond.1 hcond.2).2).symm.subset (List.mem_cons_of_mem _ hit)
      · rw [(htry_nc hcond).2.2.1]; exact hit
    have hkeep₁ : ∀ it ∈ forestItems rootsInit, it ∈ forestItems roots₁ := fun it hit =>
      hkeep_step it (W.hkeep it hit)
    have hprev₁ : ∀ p ∈ forestEntries roots₁,
        p.1.val ∈ (forestItems roots₀).map SHItem.val ∨
        ∃ t', startJ ≤ t' ∧ t' < j₀ + (t + 1) ∧ s₀.mem (L.adjBase + 2 * t' + 1) = p.1.val := by
      intro p hp
      rcases htry_ent p hp with ⟨c₀, hc₀, _⟩ | ⟨_, _, hp1, _⟩
      · rcases W.hprev (p.1, c₀) hc₀ with h0 | ⟨t', ht1, ht2, ht3⟩
        · exact .inl h0
        · exact .inr ⟨t', ht1, by omega, ht3⟩
      · refine .inr ⟨j, hj_ge', by dsimp only [j]; omega, ?_⟩
        rw [hp1]
    have hent₁ : ∀ p ∈ forestEntries roots₁,
        (∃ c₀, (p.1, c₀) ∈ forestEntries rootsInit ∧ c₀ ≤ p.2) ∨
        ∃ t' : ℕ, j₀ ≤ t' ∧ t' < j₀ + (t + 1) ∧
          ∃ eIdx : Fin m, s₀.mem (L.adjBase + 2 * t') < n ∧
            s₀.mem (L.adjBase + 2 * t' + 1) = eIdx.val ∧
            p.1.val = eIdx.val ∧ p.1.origKey = L.es[eIdx].weight ∧ p.1.origKey ≤ p.2 ∧
            edgeState0 eIdx.val = 0 ∧
            s₀.mem (L.bufBase + n + s₀.mem (L.adjBase + 2 * t')) ≠ cid := by
      intro p hp
      rcases htry_ent p hp with ⟨c₀, hc₀, hle⟩ | ⟨hcond1, hcond2, hp1, hp2⟩
      · rcases W.hent (p.1, c₀) hc₀ with ⟨c₁, hc₁, hle₁⟩ |
            ⟨t', ht1, ht2, eIdx, h1, h2, h3, h4, h5, h6, h7⟩
        · exact .inl ⟨c₁, hc₁, hle₁.trans hle⟩
        · exact .inr ⟨t', ht1, by omega, eIdx, h1, h2, h3, h4, h5.trans hle, h6, h7⟩
      · have he_eq_fin :
            L.es[s₀.mem (L.adjBase + 2 * j + 1)]'he_lt = L.es[eFin.val]'eFin.isLt := by
          have : ∀ {i₁ i₂} (h₁ : i₁ < L.es.length) (h₂ : i₂ < L.es.length),
              i₁ = i₂ → L.es[i₁]'h₁ = L.es[i₂]'h₂ := by rintro i₁ i₂ h₁ h₂ rfl; rfl
          exact this he_lt eFin.isLt heFin_id.symm
        refine .inr ⟨j, by dsimp only [j]; omega, by dsimp only [j]; omega, eFin, hnb_lt,
          heFin_id.symm, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hp1]; exact heFin_id.symm
        · rw [hp1]; simpa only [Fin.getElem_fin] using congrArg IndexedEdge.weight he_eq_fin
        · exact hsh₁.origKey_le_ckey _ hp
        · rw [heFin_id, ← hst_agree]; exact hcond1
        · rw [← hin_agree]; exact hcond2
    have hcov₁ : ∀ t' : ℕ, j₀ ≤ t' → t' < j₀ + (t + 1) →
        let nb := s₀.mem (L.adjBase + 2 * t')
        let eIdx := s₀.mem (L.adjBase + 2 * t' + 1)
        edgeState0 eIdx = 0 → s₀.mem (L.bufBase + n + nb) ≠ cid →
        ∃ p ∈ forestEntries roots₁,
          p.1.val = eIdx ∧ ∃ hlt : eIdx < m,
            p.1.origKey = (L.es[eIdx]'hlt).weight ∧ p.1.origKey ≤ p.2 := by
      intro t' ht'1 ht'2 nb eIdx hst' hnb'
      by_cases ht'_eq : t' = j
      · subst ht'_eq
        have hst_s' : s'.mem (L.bufBase + 14 * n + s₀.mem (L.adjBase + 2 * j + 1)) = 0 :=
          hst_agree.trans hst'
        have hnb_s' : s'.mem (L.bufBase + n + s₀.mem (L.adjBase + 2 * j)) ≠ cid :=
          fun heq => hnb' (hin_agree ▸ heq)
        have hperm := (htry_ic hst_s' hnb_s').2
        have hmem_it : ⟨st'.sh.itemCount + 1, s₀.mem (L.adjBase + 2 * j + 1),
            L.es[s₀.mem (L.adjBase + 2 * j + 1)].weight⟩ ∈ forestItems roots₁ :=
          hperm.symm.subset (List.mem_cons_self)
        rcases mem_forestItems_iff.mp hmem_it with ⟨c, hc⟩
        refine ⟨(_, c), hc, rfl, he_lt, rfl, ?_⟩
        exact hsh₁.origKey_le_ckey _ hc
      · rcases W.hcov t' ht'1 (by dsimp only [j] at ht'_eq; omega) hst' hnb' with
          ⟨p, hp, hp1, hlt, hp2, hp3⟩
        rcases mem_forestItems_iff.mpr ⟨p.2, hp⟩ with hmem_it
        have hmem_it₁ : p.1 ∈ forestItems roots₁ := hkeep_step p.1 hmem_it
        rcases mem_forestItems_iff.mp hmem_it₁ with ⟨c₁, hc₁⟩
        refine ⟨(p.1, c₁), hc₁, hp1, hlt, hp2, hsh₁.origKey_le_ckey _ hc₁⟩
    refine ⟨hstep_safe, hstep_vh, ⟨⟨⟨st'.idx + 1, sh1⟩, s1, t + 1⟩, ?_⟩,
      ⟨hres_eq.symm, hs'_eq.symm, by dsimp only [inv]; rw [ht_eq']⟩, ?_, hmod_step⟩
    · refine ⟨roots₁, created₁, by have := W.hidx; dsimp only; omega, htry_fr.trans W.hfr,
        hmod_next, by rw [htry_ib, W.hib], by rw [htry_nb, W.hnb], htry_rt,
        W.hic_ge.trans hic_bounds.1, by have := W.hic_le; dsimp only; omega, hsh₁, hok₁, hnd₁,
        hlen₁, hkeep₁, hprev₁, hent₁, hcov₁⟩
    · dsimp only [pot]
      rw [hcost_eq, Nat.cast_add]
      have hpot_q : (memoryCost (partTryInsertEdge tryD) s' : ℚ) +
          totalPhi partRankThreshold roots₁ ≤
            totalPhi partRankThreshold W.roots + 2445 := htry_cost
      push_cast; linarith
  let hwt₀ : ExpandIterWitness L cid ic₀ nc₀ u h₀ hInit roots₀ rootsInit s₀ edgeState0 j₀ 0
      ⟨j₀, hInit⟩ sInit :=
    ⟨rootsInit, createdInit, rfl, hfr, hmod, hib, hnb, hrtInit, le_rfl, le_rfl, hsh, hok, hnd,
      by simp, fun _ hi => hi, hprev, fun p hp => .inl ⟨p.2, hp, le_rfl⟩, fun t h1 h2 => by omega⟩
  obtain ⟨hsafe, hv, hmod_bw, ⟨⟨st', s', t'⟩, W'⟩, ⟨hst_bw, hs_bw, ht'_bw⟩, hpot_bw⟩ :=
    iterate_rat_witness_spec partExpandStep partExpandStepSafe w stepD 2450 k inv pot S hstep
      ⟨⟨⟨j₀, hInit⟩, sInit, 0⟩, hwt₀⟩ ⟨j₀, hInit⟩ sInit ⟨rfl, rfl, rfl⟩
  dsimp only [inv, pot] at hst_bw hs_bw ht'_bw hpot_bw
  dsimp only [stepD, m, pot, hwt₀] at hpot_bw
  dsimp only [stepD, m] at hsafe hv
  change ExpandIterWitness L cid ic₀ nc₀ u h₀ hInit roots₀ rootsInit s₀ edgeState0 j₀ t' st' s'
    at W'
  let W'' : ExpandIterWitness L cid ic₀ nc₀ u h₀ hInit roots₀ rootsInit s₀ edgeState0 j₀ k
      st' s' := ht'_bw ▸ W'
  have hroots_eq : W''.roots = W'.roots := by cases ht'_bw; rfl
  rw [← hroots_eq] at hpot_bw
  have hagree_res : ∀ x, x ∉ S → s'.mem x = sInit.mem x :=
    hs_bw ▸ mem_eq_of_modifies_frontier hv hmod_bw
      ((congrArg Memory.State.frontier hs_bw.symm).trans (W''.hfr.trans hfr.symm))
  have hmod_res : ∀ x, s'.mem x ≠ s₀.mem x → InSHPool ic₀ nc₀ (2 * m) (4 * m) h₀ x := fun x hx =>
    by_contra fun hxS => hx ((hagree_res x hxS).trans (by_contra fun hx0 => hxS (hmod x hx0)))
  dsimp only
  rw [← hst_bw, ← hs_bw]
  refine ⟨hsafe, hv, W''.hidx, W''.hfr, hmod_res, W''.hib, W''.hnb, W''.hrt, W''.hic_ge,
    W''.hic_le, W''.roots, W''.created, W''.hsh, hpot_bw, W''.hlen, W''.hnd, W''.hkeep, W''.hent,
    W''.hcov⟩

/-- Specification of `partExpandVertex`: expands all active incident cross edges of `u` into the
Soft Heap at amortized cost `≤ 2 + 2450 * deg(u)`. -/
theorem partExpandVertex_spec {w n : ℕ} (L : PartLayout w n)
    (cid ic₀ nc₀ : ℕ) (u : Fin n) (h₀ : SHHandle) (roots₀ : List SHTree)
    (created₀ : ℕ → ℕ) (s₀ : Memory.State) (edgeState0 : ℕ → ℕ)
    (hfr₀ : s₀.frontier = L.bufBase + (14 * n + 14 * L.es.length))
    (hib₀ : h₀.itemBase = L.itemBase) (hnb₀ : h₀.nodeBase = L.nodeBase)
    (hrt₀ : h₀.rankThreshold = partRankThreshold)
    (hsh₀ : SHInv w ic₀ nc₀ (2 * L.es.length) (4 * L.es.length) h₀ roots₀ created₀ s₀)
    (hcsr₀ : HoldsUndirCSR L.offBase L.adjBase L.es s₀.mem)
    (hin₀ : HoldsIndexedEdges L.edgeBase L.es s₀.mem)
    (hedgeSt₀ : ∀ i < L.es.length, s₀.mem (L.bufBase + 14 * n + i) = edgeState0 i)
    (hok₀ : ∀ p ∈ forestEntries roots₀, p.1.origKey ≤ p.2)
    (hsimp : ∀ e : Fin L.es.length, (L.es[e.val]'e.isLt).u ≠ (L.es[e.val]'e.isLt).v)
    (hnd₀ : ((forestItems roots₀).map SHItem.val).Nodup)
    (hno_dup₀ : ∀ p ∈ forestEntries roots₀,
      ∃ eIdx : Fin L.es.length, p.1.val = eIdx.val ∧
        ((L.es[eIdx.val]'eIdx.isLt).u = u ∨ (L.es[eIdx.val]'eIdx.isLt).v = u →
          ∃ nb : Fin n, (((L.es[eIdx.val]'eIdx.isLt).u = u ∧ (L.es[eIdx.val]'eIdx.isLt).v = nb) ∨
            ((L.es[eIdx.val]'eIdx.isLt).v = u ∧ (L.es[eIdx.val]'eIdx.isLt).u = nb)) ∧
            s₀.mem (L.bufBase + n + nb.val) = cid))
    (hcap : h₀.itemCount +
      (s₀.mem (L.offBase + u.val + 1) - s₀.mem (L.offBase + u.val)) ≤ 2 * L.es.length) :
    let d : PartExpandVertexArgs := ⟨L.toEnv, cid, u.val, h₀⟩
    let prog := partExpandVertex d
    let h' := (Memory.spec 0).clientResult s₀ prog
    let s' := (Memory.spec 0).clientState s₀ prog
    let deg := s₀.mem (L.offBase + u.val + 1) - s₀.mem (L.offBase + u.val)
    partExpandVertexSafe w d s₀ ∧
    (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ prog) ∧
    s'.frontier = s₀.frontier ∧
    Memory.WellFormed w s' ∧
    (∀ a, s'.mem a ≠ s₀.mem a →
      InSHPool ic₀ nc₀ (2 * L.es.length) (4 * L.es.length) h₀ a) ∧
    h'.itemBase = h₀.itemBase ∧ h'.nodeBase = h₀.nodeBase ∧
    h'.rankThreshold = partRankThreshold ∧
    h₀.itemCount ≤ h'.itemCount ∧ h'.itemCount ≤ h₀.itemCount + deg ∧
    ∃ roots' created',
      SHInv w ic₀ nc₀ (2 * L.es.length) (4 * L.es.length) h' roots' created' s' ∧
      (memoryCost prog s₀ : ℚ) + totalPhi partRankThreshold roots' ≤
        totalPhi partRankThreshold roots₀ + 2 + 2450 * deg ∧
      (forestItems roots').length =
        (forestItems roots₀).length + (h'.itemCount - h₀.itemCount) ∧
      ((forestItems roots').map SHItem.val).Nodup ∧
      (∀ it ∈ forestItems roots₀, it ∈ forestItems roots') ∧
      (∀ p ∈ forestEntries roots',
        (∃ c₀, (p.1, c₀) ∈ forestEntries roots₀ ∧ c₀ ≤ p.2) ∨
        ∃ eIdx : Fin L.es.length,
          p.1.val = eIdx.val ∧ p.1.origKey = L.es[eIdx].weight ∧ p.1.origKey ≤ p.2 ∧
          edgeState0 eIdx.val = 0 ∧
          ((L.es[eIdx].u = u ∧ s₀.mem (L.bufBase + n + L.es[eIdx].v.val) ≠ cid) ∨
           (L.es[eIdx].v = u ∧ s₀.mem (L.bufBase + n + L.es[eIdx].u.val) ≠ cid))) ∧
      (∀ eIdx : Fin L.es.length, edgeState0 eIdx.val = 0 →
        ((L.es[eIdx].u = u ∧ s₀.mem (L.bufBase + n + L.es[eIdx].v.val) ≠ cid) ∨
         (L.es[eIdx].v = u ∧ s₀.mem (L.bufBase + n + L.es[eIdx].u.val) ≠ cid)) →
        ∃ p ∈ forestEntries roots',
          p.1.val = eIdx.val ∧ p.1.origKey = L.es[eIdx].weight ∧ p.1.origKey ≤ p.2) := by
  let m := L.es.length
  let startJ := s₀.mem (L.offBase + u.val)
  let endJ := s₀.mem (L.offBase + u.val + 1)
  let deg := endJ - startJ
  have hle_j : startJ ≤ endJ := hcsr₀.off_mono u
  have hoff_lt : L.offBase + u.val + 1 < s₀.frontier := by
    have := L.hoff_adj; have := L.hadj_it; have := L.hit_nd; have := L.hnd_buf
    rw [hfr₀]; omega
  have hind := partExpandVertex_iter_spec L cid ic₀ nc₀ u h₀ roots₀ s₀ edgeState0 hfr₀ hib₀ hnb₀
    hcsr₀ hin₀ hedgeSt₀ hsimp hno_dup₀ deg startJ h₀ roots₀ created₀ s₀ (by omega) le_rfl
    rfl (fun _ hx => absurd rfl hx) rfl rfl hrt₀ hsh₀ hok₀ hnd₀
    (fun p hp => .inl (List.mem_map.mpr ⟨p.1, mem_forestItems_iff.mpr ⟨p.2, hp⟩, rfl⟩)) hcap
  rcases hind with ⟨hsafe_it, hv_it, _, hfr_it, hmod_it, hib_it, hnb_it, hrt_it, hic1, hic2,
    roots', created', hsh', hpot_it, hlen_it, hnd_it, hkeep_it, hent_it, hcov_it⟩
  have hsafe : partExpandVertexSafe w ⟨L.toEnv, cid, u.val, h₀⟩ s₀ := by
    rw [partExpandVertexSafe_def]
    exact ⟨L.h16, hoff_lt, hle_j, hsafe_it⟩
  have hvh : (Memory.spec w).ValidHistory s₀
      ((Memory.spec w).clientHistory s₀ (partExpandVertex ⟨L.toEnv, cid, u.val, h₀⟩)) := by
    rw [partExpandVertex_def]; dsimp only [PartLayout.toEnv, m]
    refine validHistory_read_bind (by omega) (validHistory_read_bind hoff_lt ?_)
    exact validHistory_bind_step hv_it (validHistory_pure w _ _)
  have hres_eq : (Memory.spec 0).clientResult s₀
      (partExpandVertex ⟨L.toEnv, cid, u.val, h₀⟩) =
      ((Memory.spec 0).clientResult s₀
        (iterate partExpandStep ⟨L.adjBase, L.edgeBase, L.bufBase, n, m, cid⟩
          deg ⟨startJ, h₀⟩)).sh := by
    rw [partExpandVertex_def]; dsimp only [PartLayout.toEnv, deg, m]
    rw [clientResult_bind_read, clientResult_bind_read, StateTransitionSpec.clientResult_bind,
      StateTransitionSpec.clientResult_pure]
  have hs'_eq : (Memory.spec 0).clientState s₀
      (partExpandVertex ⟨L.toEnv, cid, u.val, h₀⟩) =
      (Memory.spec 0).clientState s₀
        (iterate partExpandStep ⟨L.adjBase, L.edgeBase, L.bufBase, n, m, cid⟩
          deg ⟨startJ, h₀⟩) := by
    rw [partExpandVertex_def]; dsimp only [PartLayout.toEnv, deg, m]
    rw [clientState_bind_read, clientState_bind_read, StateTransitionSpec.clientState_bind,
      StateTransitionSpec.clientState_pure]
  have hcost_eq : memoryCost (partExpandVertex ⟨L.toEnv, cid, u.val, h₀⟩) s₀ =
      2 + memoryCost (iterate partExpandStep
        ⟨L.adjBase, L.edgeBase, L.bufBase, n, m, cid⟩ deg ⟨startJ, h₀⟩) s₀ := by
    rw [partExpandVertex_def]; dsimp only [PartLayout.toEnv, deg, startJ, endJ, m]
    rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
      memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
      memoryCost_bind', memoryCost_pure, add_zero]
    omega
  refine ⟨hsafe, hvh, by rw [hs'_eq, hfr_it], by rw [hs'_eq]; exact hsh'.wf,
    by rw [hs'_eq]; exact hmod_it, by rw [hres_eq, hib_it], by rw [hres_eq, hnb_it],
    by rw [hres_eq, hrt_it], by rw [hres_eq]; exact hic1, by rw [hres_eq]; exact hic2,
    roots', created', by rw [hres_eq, hs'_eq]; exact hsh', ?_, by rw [hres_eq]; exact hlen_it,
    hnd_it, hkeep_it, ?_, ?_⟩
  · rw [hcost_eq, Nat.cast_add]; dsimp only [deg, startJ, endJ, m] at hpot_it ⊢
    push_cast; linarith
  · intro p hp
    rcases hent_it p hp with hc₀ | ⟨t, ht1, ht2, eIdx, hnb_lt, h1, h2, h3, h4, h5, h6⟩
    · exact .inl hc₀
    · refine .inr ⟨eIdx, h2, h3, h4, h5, ?_⟩
      have hmem : (s₀.mem (L.adjBase + 2 * t), s₀.mem (L.adjBase + 2 * t + 1)) ∈
          (List.range deg).map (fun q =>
            let p := startJ + q
            (s₀.mem (L.adjBase + 2 * p), s₀.mem (L.adjBase + 2 * p + 1))) := by
        refine List.mem_map.mpr ⟨t - startJ, List.mem_range.mpr (by omega), ?_⟩
        dsimp only; rw [show startJ + (t - startJ) = t by omega]
      rw [hcsr₀.mem_slice_iff] at hmem
      rcases hmem with ⟨eFin, heFin_id, heFin_ends⟩
      have heeq : eFin = eIdx := Fin.ext (heFin_id.trans h1)
      subst heeq
      simp only [Fin.getElem_fin] at heFin_ends ⊢
      rcases heFin_ends with ⟨hu, hv⟩ | ⟨hv, hu⟩
      · exact .inl ⟨hu, by rw [hv]; exact h6⟩
      · exact .inr ⟨hv, by rw [hu]; exact h6⟩
  · intro eIdx he_st hinc
    have hmem : ((if L.es[eIdx].u = u then L.es[eIdx].v.val else L.es[eIdx].u.val), eIdx.val) ∈
        (List.range deg).map (fun q =>
          let p := startJ + q
          (s₀.mem (L.adjBase + 2 * p), s₀.mem (L.adjBase + 2 * p + 1))) := by
      rw [hcsr₀.mem_slice_iff]
      refine ⟨eIdx, rfl, ?_⟩
      simp only [Fin.getElem_fin] at hinc ⊢
      rcases hinc with ⟨hu, _⟩ | ⟨hv, _⟩
      · exact .inl ⟨hu, by simp only [hu, ↓reduceIte]⟩
      · refine .inr ⟨hv, ?_⟩
        have hne : (L.es[eIdx.val]'eIdx.isLt).u ≠ u := fun h => hsimp eIdx (h.trans hv.symm)
        simp only [hne, ↓reduceIte]
    rw [List.mem_map] at hmem
    rcases hmem with ⟨q, hq, hpair⟩
    rw [List.mem_range] at hq
    have hnb_eq : s₀.mem (L.adjBase + 2 * (startJ + q)) =
        if L.es[eIdx].u = u then L.es[eIdx].v.val else L.es[eIdx].u.val := congrArg Prod.fst hpair
    have he_eq : s₀.mem (L.adjBase + 2 * (startJ + q) + 1) = eIdx.val := congrArg Prod.snd hpair
    have hnb_ne : s₀.mem (L.bufBase + n + s₀.mem (L.adjBase + 2 * (startJ + q))) ≠ cid := by
      rw [hnb_eq]
      simp only [Fin.getElem_fin] at hinc ⊢
      rcases hinc with ⟨hu, hv⟩ | ⟨hv, hu⟩
      · simp [hu, hv]
      · have hne : (L.es[eIdx.val]'eIdx.isLt).u ≠ u := fun h => hsimp eIdx (h.trans hv.symm)
        simp [hne, hu]
    rcases hcov_it (startJ + q) (by omega) (by omega) (by rw [he_eq]; exact he_st) hnb_ne with
      ⟨p, hp, hp1, hlt, hp2, hp3⟩
    have hwt_fin : (L.es[s₀.mem (L.adjBase + 2 * (startJ + q) + 1)]'hlt).weight =
        (L.es[eIdx.val]'eIdx.isLt).weight := by
      have : ∀ {i₁ i₂} (h₁ : i₁ < L.es.length) (h₂ : i₂ < L.es.length),
          i₁ = i₂ → (L.es[i₁]'h₁).weight = (L.es[i₂]'h₂).weight := by rintro _ _ _ _ rfl; rfl
      exact this hlt eIdx.isLt he_eq
    refine ⟨p, hp, hp1.trans he_eq, ?_, hp3⟩
    simpa only [Fin.getElem_fin] using hp2.trans hwt_fin


end Cslib.Algorithms.WordRAM.MinimumSpanningForest
