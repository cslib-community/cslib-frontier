/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.Contraction
public import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.GraphOps.CSR
public import CslibFrontier.DataStructure.PriorityQueue.FibonacciHeap.Native.Reset
import CslibFrontier.Foundations.Data.List.Subperm
import Mathlib.Algebra.BigOperators.Fin

/-!
# Fredman–Tarjan Bounded-Heap Phase Layout, Workspace Invariants, and Cut/Shrinkage Lemmas

Defines the word-encoded records, static workspace layout, DJP cut/phase invariants, amortized
vertex potentials, and graph-level cut/shrinkage lemmas for a single bounded-heap contraction phase
of `[FredmanTarjan1987]` (§3) / `[PettieRamachandran2002]` (§3.4 `DenseCase`) toward `#8624`,
reused across `DenseCase/ScanOps`, `DenseCase/Scan`, and `DenseCase/Phase`.

## Main definitions

* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.DenseCase.FTCtx`,
  `FTGrowState`, `FTRunTreeArgs`, `FTPhaseArgs`, `FTPhaseOut`: faithfully word-encoded records.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.DenseCase.FTStatic`, `FTCutInv`, `FTPhaseInv`:
  static workspace framing, inner DJP cut, and outer contraction-phase invariants.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.DenseCase.vertexPot`, `growPot`, `phasePot`,
  `growRank`: amortized vertex and heap potentials and bounded-heap termination measure.

## Main results

* `MinimumSpanningForest.DenseCase.exists_extend_isMinSpanningForest_cutStep`:
  extending an MSF witness across a valid cut step.
* `MinimumSpanningForest.DenseCase.exists_cut_witness_of_nonisolated`
* `MinimumSpanningForest.DenseCase.surviving_vertices_mul_thresh_le`
* `MinimumSpanningForest.DenseCase.phasePot_zero_le`
-/

public section

namespace Cslib.Algorithms.WordRAM.MinimumSpanningForest.DenseCase

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.PriorityQueue Cslib.DataStructure.PriorityQueue.FibonacciHeap
open Cslib.DataStructure.PriorityQueue.FibonacciHeap.Native
open Cslib.Algorithms.Lean.Kruskal Cslib.Algorithms.WordRAM.MinimumSpanningForest
open Cslib.Query.MinimumSpanningForest

/-! ## Word-Encoded Structures -/

/-- Phase context passed to bounded-heap DJP subroutines. -/
structure FTCtx where
  /-- Active vertex count `n_p`. -/
  n : ℕ
  /-- Active edge count `m_p`. -/
  m : ℕ
  /-- Base address of active stride-4 `IndexedEdge` array. -/
  edgeBase : ℕ
  /-- Base address of CSR offset array `[0..n_p]`. -/
  offBase : ℕ
  /-- Base address of CSR adjacency array `[0..4 * m_p)`. -/
  adjBase : ℕ
  /-- Base address of `9 * n_p + 5`-word Fibonacci heap. -/
  fhBase : ℕ
  /-- Base address of `5 * n_p`-word scratch block (`tr, bestEdge, sup, comp, touched`). -/
  auxBase : ℕ
  /-- Base address of preallocated original-id selection buffer. -/
  selBufBase : ℕ
  /-- Heap size threshold `K_p = min n_p (2 ^ (2 * m_ref / n_p))`. -/
  thresh : ℕ

/-- Faithful nine-word encoding of `FTCtx`. -/
word_enc_structure encFTCtx : FTCtx where
  n : wordWords,
  m : wordWords,
  edgeBase : wordWords,
  offBase : wordWords,
  adjBase : wordWords,
  fhBase : wordWords,
  auxBase : wordWords,
  selBufBase : wordWords,
  thresh : wordWords

instance : WordEncoding FTCtx := ⟨9, encFTCtx⟩

/-- Inner DJP tree growth state. -/
structure FTGrowState where
  /-- Loop continuation flag (`1` to continue, `0` to stop). -/
  go : ℕ
  /-- Next unscanned vertex added to the current tree. -/
  x : ℕ
  /-- Number of vertices pushed onto `touched` for the current tree. -/
  touchedLen : ℕ
  /-- Current length of `selBuf`. -/
  selLen : ℕ
  /-- Earlier tree id merged into (`< s`), or `n_p` if not merged. -/
  jn : ℕ

/-- Faithful five-word encoding of `FTGrowState`. -/
word_enc_structure encFTGrowState : FTGrowState where
  go : wordWords,
  x : wordWords,
  touchedLen : wordWords,
  selLen : wordWords,
  jn : wordWords

instance : WordEncoding FTGrowState := ⟨5, encFTGrowState⟩

/-- Input bundle for `ftRunTree`. -/
structure FTRunTreeArgs where
  /-- Phase context. -/
  ctx : FTCtx
  /-- Root vertex `t` starting the new bounded-heap tree. -/
  root : ℕ
  /-- Number of supervertices created before vertex `t`. -/
  nComp : ℕ
  /-- Current length of `selBuf`. -/
  selLen : ℕ

/-- Faithful twelve-word encoding of `FTRunTreeArgs`. -/
word_enc_structure encFTRunTreeArgs : FTRunTreeArgs where
  ctx : encFTCtx,
  root : wordWords,
  nComp : wordWords,
  selLen : wordWords

instance : WordEncoding FTRunTreeArgs := ⟨12, encFTRunTreeArgs⟩

/-- Input arguments for `ftPhaseProg`. -/
structure FTPhaseArgs where
  /-- Active vertex count `n_p`. -/
  n : ℕ
  /-- Active edge count `m_p`. -/
  m : ℕ
  /-- Reference edge count `m_ref` for the threshold `2 * m_ref / n_p`. -/
  mRef : ℕ
  /-- Base address of active stride-4 `IndexedEdge` array. -/
  edgeBase : ℕ
  /-- Base address of CSR offset array `[0..n_p]`. -/
  offBase : ℕ
  /-- Base address of CSR adjacency array `[0..4 * m_p)`. -/
  adjBase : ℕ
  /-- Base address of preallocated selection buffer. -/
  selBufBase : ℕ
  /-- Number of edges already recorded in `selBuf`. -/
  selLen : ℕ

/-- Faithful eight-word encoding of `FTPhaseArgs`. -/
word_enc_structure encFTPhaseArgs : FTPhaseArgs where
  n : wordWords,
  m : wordWords,
  mRef : wordWords,
  edgeBase : wordWords,
  offBase : wordWords,
  adjBase : wordWords,
  selBufBase : wordWords,
  selLen : wordWords

instance : WordEncoding FTPhaseArgs := ⟨8, encFTPhaseArgs⟩

/-- Output bundle returned by `ftPhaseProg`. -/
structure FTPhaseOut where
  /-- Number of supervertices (components) produced by the phase. -/
  nComp : ℕ
  /-- Base address of the `n_p`-word `comp` map array (`comp[v] < nComp`). -/
  compBase : ℕ
  /-- Updated length of `selBuf` after appending this phase's selected edges. -/
  selLen : ℕ

/-- Faithful three-word encoding of `FTPhaseOut`. -/
word_enc_structure encFTPhaseOut : FTPhaseOut where
  nComp : wordWords,
  compBase : wordWords,
  selLen : wordWords

instance : WordEncoding FTPhaseOut := ⟨3, encFTPhaseOut⟩

/-! ## Generic `Memory.State` and `FibonacciHeap` Framing Helpers -/

/-- Updates a single memory cell while preserving `Memory.WellFormed w`. -/
theorem wellFormed_update {w a v : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : Fits w v) : Memory.WellFormed w ⟨Function.update s.mem a v, s.frontier⟩ := by
  refine ⟨hwf.frontier_fits, fun x => ?_⟩
  dsimp only
  by_cases h : x = a
  · rw [h, Function.update_self]; exact hv
  · rw [Function.update_of_ne h]; exact hwf.mem_fits x

/-- Preserves framed Fibonacci heap invariant, abstraction, and potential whenever cells inside
`footprint n base` are untouched, frontier does not shrink, and `s'.frontier` fits in `w` bits. -/
theorem framed_preserved {w n K base : ℕ} {hn : Fits w n} {hK : Fits w K} {s s' : Memory.State}
    (hinv : (framed hn hK base).inv s)
    (hmem : ∀ a ∈ footprint n base, s'.mem a = s.mem a)
    (hfr : s.frontier ≤ s'.frontier) (hfit : Fits w s'.frontier) :
    (framed hn hK base).inv s' ∧
    (framed hn hK base).abs s' = (framed hn hK base).abs s ∧
    potential n ((layout n base).abs s') = potential n ((layout n base).abs s) := by
  have hroom : Fits w (s'.frontier + (framed hn hK base).room s') := by
    rw [framed_room]; exact hfit
  obtain ⟨hinv', habs', _⟩ := (framed hn hK base).congr hinv hmem hfr hroom
  have hpot := potential_local hn hK base hinv hmem hfr hroom
  exact ⟨hinv', habs', by simpa only [Nat.add_zero] using hpot⟩

/-! ## List, Edge-Partition, and MSF Cut-Step Lemmas -/

/-- Any duplicate-free list of indices into `es` yields a subpermutation of `es`. -/
theorem selIdxs_subperm_es {n : ℕ} {es : List (IndexedEdge n)} {selIdxs : List (Fin es.length)}
    (hnd : selIdxs.Nodup) : (selIdxs.map fun i => es[i.val]).Subperm es := by
  have h1 : selIdxs.Subperm (List.finRange es.length) :=
    hnd.subperm fun x _ => List.mem_finRange x
  have h2 := List.subperm_map (fun i : Fin es.length => es[i.val]) h1
  rwa [List.map_getElem_finRange] at h2

/-- Relation characterization of `edgePartition (L ++ [e])` in terms of `edgePartition L`. -/
theorem edgePartition_append_single_rel {n : ℕ} (L : List (WeightedEdge n ℕ))
    (e : WeightedEdge n ℕ) (a b : Fin n) :
    (edgePartition (L ++ [e])).rel a b = true ↔
      (edgePartition L).rel a b = true ∨
      ((edgePartition L).rel a e.u = true ∧ (edgePartition L).rel e.v b = true) ∨
      ((edgePartition L).rel a e.v = true ∧ (edgePartition L).rel e.u b = true) := by
  simp only [edgePartition, edgePartitionFrom_append, edgePartitionFrom_cons,
    edgePartitionFrom_nil, DisjointSet.Partition.rel_merge_eq_true]

/-- Cut-step extension for Fredman–Tarjan MSF construction: adding a lightest crossing edge out
of a current tree component `A` preserves subpermutation, acyclicity, and MSF extendability. -/
theorem exists_extend_isMinSpanningForest_cutStep {n : ℕ}
    (es sel : List (WeightedEdge n ℕ))
    (hsel_sub : sel.Subperm es) (hsel_ac : IsAcyclic sel)
    (hext : ∃ F_ext : List (WeightedEdge n ℕ), IsMinSpanningForest es (sel ++ F_ext))
    (A : Finset (Fin n)) (hA_ne : A.Nonempty)
    (hA_comp : ∀ x ∈ A, ∀ y : Fin n, (edgePartition sel).rel x y = true ↔ y ∈ A)
    (e : WeightedEdge n ℕ) (he : e ∈ es) (hcut : e.u ∈ A ↔ e.v ∉ A)
    (hmin : ∀ f ∈ es, (f.u ∈ A ↔ f.v ∉ A) → e.weight ≤ f.weight) :
    (sel ++ [e]).Subperm es ∧ IsAcyclic (sel ++ [e]) ∧
      ∃ F_ext : List (WeightedEdge n ℕ), IsMinSpanningForest es ((sel ++ [e]) ++ F_ext) := by
  classical
  let p := edgePartition sel
  let S : Setoid (Fin n) := ⟨fun x y => p.rel x y = true,
    ⟨fun x => p.refl x, fun h => p.symm h, fun h1 h2 => p.trans h1 h2⟩⟩
  let qEquiv := Fintype.equivFin (Quotient S)
  let c : Fin n → Fin (Fintype.card (Quotient S)) := fun x => qEquiv (Quotient.mk S x)
  have hc_rel : ∀ x y : Fin n, c x = c y ↔ p.rel x y = true := fun x y => by
    dsimp only [c]; rw [qEquiv.apply_eq_iff_eq, Quotient.eq]; rfl
  have hc_surj : Function.Surjective c := fun y => by
    obtain ⟨x, hx⟩ := Quotient.exists_rep (qEquiv.symm y)
    exact ⟨x, by dsimp only [c]; rw [hx]; simp⟩
  obtain ⟨r, hrA⟩ := hA_ne
  let rC : Fin (Fintype.card (Quotient S)) := c r
  have hc_eq_rC : ∀ x : Fin n, c x = rC ↔ x ∈ A := fun x => by
    rw [hc_rel]
    have hs : p.rel x r = p.rel r x := Bool.eq_iff_iff.mpr ⟨p.symm, p.symm⟩
    change p.rel x r = true ↔ x ∈ A
    rw [hs]
    exact hA_comp r hrA x
  let esC := contractEdgeList c es
  let eC := contractEdge c e
  have heC_mem : eC ∈ esC := List.mem_map.mpr ⟨e, he, rfl⟩
  have hcutC : eC.u ∈ ({rC} : Finset _) ↔ eC.v ∉ ({rC} : Finset _) := by
    simp only [Finset.mem_singleton, eC, contractEdge, hc_eq_rC]
    exact hcut
  have hminC : ∀ fC ∈ esC, (fC.u ∈ ({rC} : Finset _) ↔ fC.v ∉ ({rC} : Finset _)) →
      eC.weight ≤ fC.weight := by
    intro fC hfC hcrossC
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hfC
    simp only [Finset.mem_singleton, contractEdge, hc_eq_rC] at hcrossC
    exact hmin f hf hcrossC
  obtain ⟨F_c, hFc_msf⟩ := exists_extend_isMinSpanningForest_of_cutStep esC eC heC_mem
    {rC} hcutC hminC
  have hes_perm : (e :: es.erase e).Perm es := (List.perm_cons_erase he).symm
  have hesC_perm : (eC :: (es.erase e).map (contractEdge c)).Perm esC := by
    simpa only [esC, contractEdgeList, List.map_cons] using hes_perm.map (contractEdge c)
  have hFc_sub_erase : F_c.Subperm ((es.erase e).map (contractEdge c)) := by
    have h1 : (eC :: F_c).Subperm (eC :: (es.erase e).map (contractEdge c)) := by
      obtain ⟨zs, hp, hsl⟩ := List.subperm_iff.mp hFc_msf.1.1
      exact List.subperm_iff.mpr ⟨zs, hp.trans hesC_perm.symm, hsl⟩
    have h2 := (List.cons_subperm_iff_subperm_erase.mp h1).2
    rwa [List.erase_cons_head] at h2
  obtain ⟨L, hL_sub, hL_map⟩ := hFc_sub_erase.exists_map
  have heL_sub : (e :: L).Subperm es := by
    obtain ⟨zs, hp, hsl⟩ := List.subperm_iff.mp hL_sub
    exact List.subperm_iff.mpr ⟨e :: zs, (List.Perm.cons e hp).trans hes_perm,
      List.Sublist.cons_cons e hsl⟩
  have hcomb_msf : IsMinSpanningForest es (sel ++ (e :: L)) := by
    refine isMinSpanningForest_append_of_contract es sel (e :: L) c hsel_sub hsel_ac
      hc_rel hc_surj hext heL_sub ?_
    have hFc' : IsMinSpanningForest (contractEdgeList c es) (eC :: F_c) := hFc_msf
    simpa only [contractEdgeList, List.map_cons, hL_map] using hFc'
  have he_not_sel : e ∉ sel := by
    intro he_sel
    have hrel : p.rel e.u e.v = true :=
      (rel_edgePartition_iff_eqvGen sel e.u e.v).mpr (.rel _ _ ⟨e, he_sel, rfl, rfl⟩)
    have heqA : e.u ∈ A ↔ e.v ∈ A := by
      rw [← hc_eq_rC e.u, ← hc_eq_rC e.v, (hc_rel e.u e.v).mpr hrel]
    by_cases hu : e.u ∈ A
    · exact hcut.mp hu (heqA.mp hu)
    · exact hu (hcut.mpr fun hv => hu (heqA.mpr hv))
  have hdisj_e : List.Disjoint sel [e] := by
    intro x hx hx1
    rw [List.mem_singleton] at hx1
    subst hx1
    exact he_not_sel hx
  refine ⟨hsel_sub.append_of_disjoint (List.singleton_sublist.mpr he).subperm hdisj_e, ?_, ⟨L, ?_⟩⟩
  · exact isAcyclic_subperm (List.sublist_append_left (sel ++ [e]) L).subperm
      (by simpa only [List.append_assoc, List.singleton_append] using hcomb_msf.1.2.1)
  · simpa only [List.append_assoc, List.singleton_append] using hcomb_msf

private theorem holdsUndirCSR_sum_deg {n offBase adjBase : ℕ} {es : List (IndexedEdge n)}
    {mem : ℕ → ℕ} (hcsr : HoldsUndirCSR offBase adjBase es mem) :
    ∑ v : Fin n, (mem (offBase + v.val + 1) - mem (offBase + v.val)) = 2 * es.length := by
  have hgen : ∀ k ≤ n, ∑ v : Fin k, (mem (offBase + v.val + 1) - mem (offBase + v.val)) =
      mem (offBase + k) - mem offBase := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [ih (by omega)]
      have hle0 : mem offBase ≤ mem (offBase + k) := by
        have := hcsr.off_zero; omega
      have hle1 : mem (offBase + k) ≤ mem (offBase + (k + 1)) := by
        rw [← Nat.add_assoc]; exact hcsr.off_mono ⟨k, hk⟩
      have hass : offBase + k + 1 = offBase + (k + 1) := Nat.add_assoc _ _ _
      rw [hass]
      omega
  have h1 := hgen n le_rfl
  rw [hcsr.off_zero, hcsr.off_end, Nat.sub_zero] at h1
  exact h1

/-- Extracts a large-neighborhood cut witness for any surviving non-isolated supervertex `lift y`
using loop-freeness of `esDedup` and the Fredman–Tarjan degree alternative `hdeg`. -/
theorem exists_cut_witness_of_nonisolated {n nComp nOut thresh : ℕ}
    {es : List (IndexedEdge n)} {compFn : Fin n → Fin nComp}
    {esCon esDedup : List (IndexedEdge nComp)}
    {lift : Fin nOut → Fin nComp} {esOut : List (IndexedEdge nOut)}
    (hdeg : ∀ c : Fin nComp,
      (∀ e ∈ es, compFn e.u = c ↔ compFn e.v = c) ∨
      ∃ A Z : Finset (Fin n),
        (∀ u ∈ A, compFn u = c) ∧
        thresh + 1 ≤ Z.card ∧
        ∀ z ∈ Z, z ∉ A ∧ ∃ e ∈ es, (e.u ∈ A ∧ e.v = z) ∨ (e.v ∈ A ∧ e.u = z))
    (hes_con : es.map (fun e => ⟨compFn e.u, compFn e.v, e.weight, e.id⟩) = esCon)
    (hdedup_sub : esDedup.Subperm esCon)
    (hdedup_noloop : ∀ e ∈ esDedup, e.u ≠ e.v)
    (hes_out : esOut.map (fun e => ⟨lift e.u, lift e.v, e.weight, e.id⟩) = esDedup)
    {y : Fin nOut} (hy : ∃ e ∈ esOut, e.u = y ∨ e.v = y) :
    ∃ A Z : Finset (Fin n),
      (∀ u ∈ A, compFn u = lift y) ∧
      thresh + 1 ≤ Z.card ∧
      ∀ z ∈ Z, z ∉ A ∧ ∃ e ∈ es, (e.u ∈ A ∧ e.v = z) ∨ (e.v ∈ A ∧ e.u = z) := by
  obtain ⟨eOut, heOut, hinc⟩ := hy
  let eD : IndexedEdge nComp := ⟨lift eOut.u, lift eOut.v, eOut.weight, eOut.id⟩
  have heD_mem : eD ∈ esDedup := hes_out ▸ List.mem_map.mpr ⟨eOut, heOut, rfl⟩
  have hno := hdedup_noloop eD heD_mem
  have heC_mem : eD ∈ esCon := hdedup_sub.subset heD_mem
  rw [← hes_con, List.mem_map] at heC_mem
  obtain ⟨e0, he0, he0_eq⟩ := heC_mem
  have hne : compFn e0.u ≠ compFn e0.v := by
    intro h; apply hno
    exact (congrArg IndexedEdge.u he0_eq).symm.trans (h.trans (congrArg IndexedEdge.v he0_eq))
  have hnot_cl : ¬(∀ e ∈ es, compFn e.u = lift y ↔ compFn e.v = lift y) := by
    intro hcl
    have hu0 : compFn e0.u = lift eOut.u := congrArg IndexedEdge.u he0_eq
    have hv0 : compFn e0.v = lift eOut.v := congrArg IndexedEdge.v he0_eq
    rcases hinc with rfl | rfl
    · exact hne (hu0.trans ((hcl e0 he0).mp hu0).symm)
    · exact hne (((hcl e0 he0).mpr hv0).trans hv0.symm)
  rcases hdeg (lift y) with hcl | hwit
  · exact absurd hcl hnot_cl
  · exact hwit

/-- Surviving non-isolated vertices satisfy `nOut * (thresh + 1) ≤ 2 * es.length`. -/
theorem surviving_vertices_mul_thresh_le {n nComp nOut thresh : ℕ}
    {es : List (IndexedEdge n)} {compFn : Fin n → Fin nComp}
    {esCon esDedup : List (IndexedEdge nComp)}
    {lift : Fin nOut → Fin nComp} {esOut : List (IndexedEdge nOut)}
    (hdeg : ∀ c : Fin nComp,
      (∀ e ∈ es, compFn e.u = c ↔ compFn e.v = c) ∨
      ∃ A Z : Finset (Fin n),
        (∀ u ∈ A, compFn u = c) ∧
        thresh + 1 ≤ Z.card ∧
        ∀ z ∈ Z, z ∉ A ∧ ∃ e ∈ es, (e.u ∈ A ∧ e.v = z) ∨ (e.v ∈ A ∧ e.u = z))
    (hes_con : es.map (fun e => ⟨compFn e.u, compFn e.v, e.weight, e.id⟩) = esCon)
    (hdedup_sub : esDedup.Subperm esCon)
    (hdedup_noloop : ∀ e ∈ esDedup, e.u ≠ e.v)
    (hlift_inj : Function.Injective lift)
    (hes_out : esOut.map (fun e => ⟨lift e.u, lift e.v, e.weight, e.id⟩) = esDedup)
    (hnoniso : ∀ y : Fin nOut, ∃ e ∈ esOut, e.u = y ∨ e.v = y) :
    nOut * (thresh + 1) ≤ 2 * es.length := by
  classical
  have hwit : ∀ y : Fin nOut, ∃ E : Finset (Fin es.length × Bool),
      thresh + 1 ≤ E.card ∧
      ∀ p ∈ E, compFn (if p.2 then es[p.1.val].u else es[p.1.val].v) = lift y := by
    intro y
    obtain ⟨Ay, Zy, hAy, hZy_card, hZy_nbr⟩ :=
      exists_cut_witness_of_nonisolated hdeg hes_con hdedup_sub hdedup_noloop hes_out (hnoniso y)
    have hchoose : ∀ z : Fin n, z ∈ Zy → ∃ p : Fin es.length × Bool,
        compFn (if p.2 then es[p.1.val].u else es[p.1.val].v) = lift y ∧
        (if p.2 then es[p.1.val].v else es[p.1.val].u) = z := by
      intro z hz
      obtain ⟨_, e, he, hend⟩ := hZy_nbr z hz
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp he
      rcases hend with ⟨hu, hv⟩ | ⟨hv, hu⟩
      · exact ⟨(⟨i, hi⟩, true), hAy _ hu, hv⟩
      · exact ⟨(⟨i, hi⟩, false), hAy _ hv, hu⟩
    choose f hf using fun z : {z // z ∈ Zy} => hchoose z.val z.property
    refine ⟨Zy.attach.image f, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ fun a b hab => by
        have ha := (hf a).2
        have hb := (hf b).2
        rw [hab] at ha
        exact Subtype.ext (ha.symm.trans hb), Finset.card_attach]
      exact hZy_card
    · intro p hp
      rw [Finset.mem_image] at hp
      obtain ⟨a, _, rfl⟩ := hp
      exact (hf a).1
  choose E hE_card hE_comp using hwit
  have hdisj : ∀ y₁ ∈ (Finset.univ : Finset (Fin nOut)),
      ∀ y₂ ∈ (Finset.univ : Finset (Fin nOut)), y₁ ≠ y₂ → Disjoint (E y₁) (E y₂) := by
    intro y₁ _ y₂ _ hne
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    exact hne (hlift_inj ((hE_comp y₁ p hp1).symm.trans (hE_comp y₂ p hp2)))
  have hsum_le : nOut * (thresh + 1) ≤ (Finset.univ.biUnion E).card := by
    rw [Finset.card_biUnion hdisj]
    have h1 : nOut * (thresh + 1) = ∑ _ : Fin nOut, (thresh + 1) := by
      simp [Finset.sum_const, Fintype.card_fin]
    rw [h1]
    exact Finset.sum_le_sum fun y _ => hE_card y
  have hcard_univ : (Finset.univ.biUnion E).card ≤ 2 * es.length := by
    refine (Finset.card_le_univ _).trans_eq ?_
    simp [Fintype.card_prod, Fintype.card_fin, mul_comm]
  exact hsum_le.trans hcard_univ

/-! ## Workspace Sets, Invariants, and Potentials -/

/-- Set of vertices currently assigned to tree `t`. -/
def trSet (auxBase n : ℕ) (t : Fin n) (mem : ℕ → ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun v => mem (auxBase + v.val) = t.val

/-- Set of vertices visited by any tree strictly earlier than `sLim`. -/
def visitedSet (auxBase n sLim : ℕ) (mem : ℕ → ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun v => mem (auxBase + v.val) < sLim

/-- List of the first `touchedLen` entries written to `touched`. -/
def touchedList (auxBase n touchedLen : ℕ) (mem : ℕ → ℕ) : List ℕ :=
  (List.range touchedLen).map fun i => mem (auxBase + 4 * n + i)

/-- Per-vertex potential credit paying for scanning `v`, inserting/decreasing/extracting `v`, and
later resetting `v`. -/
def vertexPot (ctx : FTCtx) (n mRef : ℕ) (v : Fin n) (mem : ℕ → ℕ) : ℕ :=
  117 * (mem (ctx.offBase + v.val + 1) - mem (ctx.offBase + v.val)) + 130 + 92 * ((2 * mRef) / n)

/-- Inner bounded-heap DJP loop potential for tree `t`. -/
def growPot (ctx : FTCtx) (n mRef : ℕ) (t : Fin n) (st : FTGrowState) (s : Memory.State) : ℕ :=
  potential n ((layout n ctx.fhBase).abs s) +
  2 * st.touchedLen +
  ∑ v : Fin n,
    if s.mem (ctx.auxBase + v.val) = t.val ∧ ¬(st.go = 1 ∧ v.val = st.x) then 0
    else vertexPot ctx n mRef v s.mem

/-- Inner bounded-heap DJP loop termination rank for tree `t`. -/
def growRank (ctx : FTCtx) (n : ℕ) (t : Fin n) (st : FTGrowState) (s : Memory.State) : ℕ :=
  if st.go = 0 then 0 else n + 1 - (trSet ctx.auxBase n t s.mem).card

/-- Outer phase vertex-scan potential at cursor `sLim`. -/
def phasePot (ctx : FTCtx) (n mRef sLim : ℕ) (mem : ℕ → ℕ) : ℕ :=
  (n - sLim) * 8 +
  ∑ v : Fin n,
    if mem (ctx.auxBase + v.val) < sLim then 0
    else vertexPot ctx n mRef v mem

/-- Membership characterization for `trSet`. -/
@[simp] theorem mem_trSet {auxBase n : ℕ} {t v : Fin n} {mem : ℕ → ℕ} :
    v ∈ trSet auxBase n t mem ↔ mem (auxBase + v.val) = t.val := by
  simp only [trSet, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Membership characterization for `visitedSet`. -/
@[simp] theorem mem_visitedSet {auxBase n sLim : ℕ} {v : Fin n} {mem : ℕ → ℕ} :
    v ∈ visitedSet auxBase n sLim mem ↔ mem (auxBase + v.val) < sLim := by
  simp only [visitedSet, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Definitional equation for `touchedList`. -/
theorem touchedList_eq (auxBase n touchedLen : ℕ) (mem : ℕ → ℕ) :
    touchedList auxBase n touchedLen mem =
      (List.range touchedLen).map fun i => mem (auxBase + 4 * n + i) := by
  simp only [touchedList]

/-- Congruence for `touchedList` under agreement on `[auxBase + 4 * n, auxBase + 4 * n + tl)`. -/
theorem touchedList_congr {auxBase n tl : ℕ} {m₁ m₂ : ℕ → ℕ}
    (h : ∀ i < tl, m₁ (auxBase + 4 * n + i) = m₂ (auxBase + 4 * n + i)) :
    touchedList auxBase n tl m₁ = touchedList auxBase n tl m₂ := by
  simp only [touchedList_eq]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

/-- Definitional equation for `vertexPot`. -/
theorem vertexPot_eq (ctx : FTCtx) (n mRef : ℕ) (v : Fin n) (mem : ℕ → ℕ) :
    vertexPot ctx n mRef v mem =
      117 * (mem (ctx.offBase + v.val + 1) - mem (ctx.offBase + v.val)) + 130 +
        92 * ((2 * mRef) / n) := by
  simp only [vertexPot]

/-- Definitional equation for `growPot`. -/
theorem growPot_eq (ctx : FTCtx) (n mRef : ℕ) (t : Fin n) (st : FTGrowState)
    (s : Memory.State) :
    growPot ctx n mRef t st s =
      potential n ((layout n ctx.fhBase).abs s) + 2 * st.touchedLen +
        ∑ v : Fin n,
          if s.mem (ctx.auxBase + v.val) = t.val ∧ ¬(st.go = 1 ∧ v.val = st.x) then 0
          else vertexPot ctx n mRef v s.mem := by
  simp only [growPot]

/-- Definitional equation for `growRank`. -/
theorem growRank_eq (ctx : FTCtx) (n : ℕ) (t : Fin n) (st : FTGrowState) (s : Memory.State) :
    growRank ctx n t st s =
      if st.go = 0 then 0 else n + 1 - (trSet ctx.auxBase n t s.mem).card := by
  simp only [growRank]

/-- Definitional equation for `phasePot`. -/
theorem phasePot_eq (ctx : FTCtx) (n mRef sLim : ℕ) (mem : ℕ → ℕ) :
    phasePot ctx n mRef sLim mem =
      (n - sLim) * 8 +
        ∑ v : Fin n,
          if mem (ctx.auxBase + v.val) < sLim then 0
          else vertexPot ctx n mRef v mem := by
  simp only [phasePot]

/-- Static layout, fit, disjointness, input, and threshold hypotheses shared across a phase. -/
structure FTStatic (w n K mRef selLen0 : ℕ) (ctx : FTCtx)
    (es : List (IndexedEdge n)) (s : Memory.State) : Prop where
  /-- Sixteen fits in `w`-bit words. -/
  fit16 : Fits w 16
  /-- Context `n` matches graph vertex count `n`. -/
  cn : ctx.n = n
  /-- Context `m` matches graph edge count `es.length`. -/
  cm : ctx.m = es.length
  /-- Vertex count `n` fits in `w`-bit words. -/
  hn : Fits w n
  /-- Key bound `K` fits in `w`-bit words. -/
  hK : Fits w K
  /-- Heap block end fits in `w`-bit words. -/
  fitFh : Fits w (ctx.fhBase + (9 * n + 5))
  /-- Auxiliary block end fits in `w`-bit words. -/
  fitAux : Fits w (ctx.auxBase + 5 * n)
  /-- CSR offset array end fits in `w`-bit words. -/
  fitOff : Fits w (ctx.offBase + n + 1)
  /-- CSR adjacency array end fits in `w`-bit words. -/
  fitAdj : Fits w (ctx.adjBase + 4 * es.length)
  /-- Edge array end fits in `w`-bit words. -/
  fitEdge : Fits w (ctx.edgeBase + 4 * es.length)
  /-- Twice edge count plus one fits in `w`-bit words. -/
  fit2m : Fits w (2 * es.length + 1)
  /-- Maximum selection length increment fits in `w`-bit words. -/
  fitSel : Fits w (selLen0 + n + 1)
  /-- CSR offsets lie below `s.frontier`. -/
  offFr : ctx.offBase + n + 1 ≤ s.frontier
  /-- CSR adjacency lies below `s.frontier`. -/
  adjFr : ctx.adjBase + 4 * es.length ≤ s.frontier
  /-- Edge array lies below `s.frontier`. -/
  edgeFr : ctx.edgeBase + 4 * es.length ≤ s.frontier
  /-- Auxiliary block lies below `s.frontier`. -/
  auxFr : ctx.auxBase + 5 * n ≤ s.frontier
  /-- Reserved selection buffer slice lies below `s.frontier`. -/
  selFr : ctx.selBufBase + selLen0 + n ≤ s.frontier
  /-- Heap block lies strictly below auxiliary block. -/
  fhLtAux : ctx.fhBase + (9 * n + 5) ≤ ctx.auxBase
  /-- Edge array lies strictly below heap block. -/
  edgeLtFh : ctx.edgeBase + 4 * es.length ≤ ctx.fhBase
  /-- CSR offsets lie strictly below heap block. -/
  offLtFh : ctx.offBase + n + 1 ≤ ctx.fhBase
  /-- CSR adjacency lies strictly below heap block. -/
  adjLtFh : ctx.adjBase + 4 * es.length ≤ ctx.fhBase
  /-- Selection buffer slice is disjoint from heap block. -/
  selDisjFh : ctx.selBufBase + selLen0 + n ≤ ctx.fhBase ∨
    ctx.fhBase + (9 * n + 5) ≤ ctx.selBufBase + selLen0
  /-- Selection buffer slice is disjoint from auxiliary block. -/
  selDisjAux : ctx.selBufBase + selLen0 + n ≤ ctx.auxBase ∨
    ctx.auxBase + 5 * n ≤ ctx.selBufBase + selLen0
  /-- Selection buffer slice is disjoint from edge array. -/
  selDisjEdge : ctx.selBufBase + selLen0 + n ≤ ctx.edgeBase ∨
    ctx.edgeBase + 4 * es.length ≤ ctx.selBufBase + selLen0
  /-- Selection buffer slice is disjoint from CSR offsets. -/
  selDisjOff : ctx.selBufBase + selLen0 + n ≤ ctx.offBase ∨
    ctx.offBase + n + 1 ≤ ctx.selBufBase + selLen0
  /-- Selection buffer slice is disjoint from CSR adjacency. -/
  selDisjAdj : ctx.selBufBase + selLen0 + n ≤ ctx.adjBase ∨
    ctx.adjBase + 4 * es.length ≤ ctx.selBufBase + selLen0
  /-- Memory stores `es` in stride-4 layout at `ctx.edgeBase`. -/
  hin : HoldsIndexedEdges ctx.edgeBase es s.mem
  /-- Memory stores undirected CSR for `es` at `ctx.offBase`, `ctx.adjBase`. -/
  hcsr : HoldsUndirCSR ctx.offBase ctx.adjBase es s.mem
  /-- All edge weights are bounded by `K`. -/
  hKes : ∀ e ∈ es, e.weight ≤ K
  /-- Heap size threshold does not exceed `2 ^ ((2 * mRef) / n)`. -/
  threshLe : ctx.thresh ≤ 2 ^ ((2 * mRef) / n)

/-- Transports `FTStatic` across a frontier-preserving/non-shrinking step that preserves the
edge and CSR regions. -/
theorem FTStatic.of_step {w n K mRef selLen0 : ℕ} {ctx : FTCtx}
    {es : List (IndexedEdge n)} {s s' : Memory.State}
    (hs : FTStatic w n K mRef selLen0 ctx es s) (hfr : s.frontier ≤ s'.frontier)
    (hmem_ro : ∀ a,
      (ctx.edgeBase ≤ a ∧ a < ctx.edgeBase + 4 * es.length) ∨
      (ctx.offBase ≤ a ∧ a < ctx.offBase + n + 1) ∨
      (ctx.adjBase ≤ a ∧ a < ctx.adjBase + 4 * es.length) →
      s'.mem a = s.mem a) :
    FTStatic w n K mRef selLen0 ctx es s' :=
  { fit16 := hs.fit16
    cn := hs.cn
    cm := hs.cm
    hn := hs.hn
    hK := hs.hK
    fitFh := hs.fitFh
    fitAux := hs.fitAux
    fitOff := hs.fitOff
    fitAdj := hs.fitAdj
    fitEdge := hs.fitEdge
    fit2m := hs.fit2m
    fitSel := hs.fitSel
    offFr := hs.offFr.trans hfr
    adjFr := hs.adjFr.trans hfr
    edgeFr := hs.edgeFr.trans hfr
    auxFr := hs.auxFr.trans hfr
    selFr := hs.selFr.trans hfr
    fhLtAux := hs.fhLtAux
    edgeLtFh := hs.edgeLtFh
    offLtFh := hs.offLtFh
    adjLtFh := hs.adjLtFh
    selDisjFh := hs.selDisjFh
    selDisjAux := hs.selDisjAux
    selDisjEdge := hs.selDisjEdge
    selDisjOff := hs.selDisjOff
    selDisjAdj := hs.selDisjAdj
    hin := hs.hin.congr fun a h1 h2 => hmem_ro a (.inl ⟨h1, h2⟩)
    hcsr := hs.hcsr.congr (fun a h1 h2 => hmem_ro a (.inr (.inl ⟨h1, h2⟩)))
      (fun a h1 h2 => hmem_ro a (.inr (.inr ⟨h1, h2⟩)))
    hKes := hs.hKes
    threshLe := hs.threshLe }

/-- Transports `FTStatic` across a step modifying only `footprint n ctx.fhBase`,
`[ctx.auxBase, ctx.auxBase + 5 * n)`, and `[ctx.selBufBase + selLen0, ... + n)`. -/
theorem FTStatic.of_workMod {w n K mRef selLen0 : ℕ} {ctx : FTCtx}
    {es : List (IndexedEdge n)} {s s' : Memory.State}
    (hs : FTStatic w n K mRef selLen0 ctx es s) (hfr : s.frontier ≤ s'.frontier)
    (hmod : ∀ a, a ∉ footprint n ctx.fhBase →
      (a < ctx.auxBase ∨ ctx.auxBase + 5 * n ≤ a) →
      (a < ctx.selBufBase + selLen0 ∨ ctx.selBufBase + selLen0 + n ≤ a) →
      s'.mem a = s.mem a) :
    FTStatic w n K mRef selLen0 ctx es s' :=
  hs.of_step hfr fun a ha => hmod a
    (by
      simp only [footprint, Finset.mem_Ico]
      rcases ha with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩
      · have := hs.edgeLtFh; omega
      · have := hs.offLtFh; omega
      · have := hs.adjLtFh; omega)
    (by
      have := hs.fhLtAux
      rcases ha with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩
      · left; have := hs.edgeLtFh; omega
      · left; have := hs.offLtFh; omega
      · left; have := hs.adjLtFh; omega)
    (by
      rcases ha with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩
      · rcases hs.selDisjEdge with h | h <;> [right; left] <;> omega
      · rcases hs.selDisjOff with h | h <;> [right; left] <;> omega
      · rcases hs.selDisjAdj with h | h <;> [right; left] <;> omega)

/-- Cut invariant maintained across scanning edges leaving tree `t`. -/
structure FTCutInv {w n K : ℕ} (hn : Fits w n) (hK : Fits w K)
    (ctx : FTCtx) (es : List (IndexedEdge n)) (t : Fin n) (scanned : Finset (Fin n))
    (touchedLen : ℕ) (s : Memory.State) : Prop where
  /-- Fibonacci heap invariant holds at `ctx.fhBase`. -/
  hinv : (framed hn hK ctx.fhBase).inv s
  /-- Number of touched entries is at most `n`. -/
  htl_le : touchedLen ≤ n
  /-- Every entry in `touched` is a valid vertex index `< n`. -/
  htouched_lt : ∀ i < touchedLen, s.mem (ctx.auxBase + 4 * n + i) < n
  /-- Entries in `touched` are pairwise distinct. -/
  htouched_nd : (touchedList ctx.auxBase n touchedLen s.mem).Nodup
  /-- Root vertex `t` is not in `touched`. -/
  htouched_ne_t : ∀ i < touchedLen, s.mem (ctx.auxBase + 4 * n + i) ≠ t.val
  /-- Every touched vertex is currently in the heap or already merged into `t`. -/
  htouched_in : ∀ i < touchedLen, ∀ (hv : s.mem (ctx.auxBase + 4 * n + i) < n),
    ((framed hn hK ctx.fhBase).abs s ⟨_, hv⟩).isSome ∨
      (⟨_, hv⟩ : Fin n) ∈ trSet ctx.auxBase n t s.mem
  /-- Every heap element appears in `touched`. -/
  htouched_cov : ∀ v : Fin n, ((framed hn hK ctx.fhBase).abs s v).isSome →
    ∃ i < touchedLen, s.mem (ctx.auxBase + 4 * n + i) = v.val
  /-- Every heap entry `(v, kv)` corresponds to a cut edge `(u ∈ T_t, v)` of weight `kv`. -/
  hheap_cut : ∀ v : Fin n, ∀ kv, (framed hn hK ctx.fhBase).abs s v = some kv →
    s.mem (ctx.auxBase + v.val) ≠ t.val ∧
    ∃ eIdx : Fin es.length, s.mem (ctx.auxBase + n + v.val) = eIdx.val ∧
      es[eIdx.val].weight = kv ∧
      ((es[eIdx.val].u ∈ trSet ctx.auxBase n t s.mem ∧ es[eIdx.val].v = v) ∨
       (es[eIdx.val].v ∈ trSet ctx.auxBase n t s.mem ∧ es[eIdx.val].u = v))
  /-- Every edge leaving a `scanned` vertex is witnessed in the heap with key `≤ e.weight`. -/
  hscanned_cov : ∀ u ∈ scanned, ∀ e ∈ es,
    ((e.u = u ∧ e.v ∉ trSet ctx.auxBase n t s.mem) →
      ∃ kz, (framed hn hK ctx.fhBase).abs s e.v = some kz ∧ kz ≤ e.weight) ∧
    ((e.v = u ∧ e.u ∉ trSet ctx.auxBase n t s.mem) →
      ∃ kz, (framed hn hK ctx.fhBase).abs s e.u = some kz ∧ kz ≤ e.weight)

/-- Outer phase invariant across tree sweeps `0 .. sLim`. -/
structure FTPhaseInv {n : ℕ} (ctx : FTCtx) (es : List (IndexedEdge n))
    (sLim nComp selLen0 selLen : ℕ) (selIdxs : List (Fin es.length))
    (mem : ℕ → ℕ) : Prop where
  /-- Every `tr[v]` is either `< sLim` or unassigned (`n`). -/
  hbound : ∀ v : Fin n, mem (ctx.auxBase + v.val) < sLim ∨ mem (ctx.auxBase + v.val) = n
  /-- Every vertex `< sLim` has already been assigned to a tree `< sLim`. -/
  hprev_vis : ∀ v : Fin n, v.val < sLim → mem (ctx.auxBase + v.val) < sLim
  /-- Component count does not exceed `sLim`. -/
  hncomp_le : nComp ≤ sLim
  /-- Current selection length equals initial offset plus selected edges count. -/
  hsel_len : selLen = selLen0 + selIdxs.length
  /-- Euler relation across visited trees: `|E| + #components = |visited|`. -/
  hsel_card : selIdxs.length + nComp = (visitedSet ctx.auxBase n sLim mem).card
  /-- Selected edge indices are duplicate-free. -/
  hsel_nd : selIdxs.Nodup
  /-- Both endpoints of every selected edge lie in `visitedSet`. -/
  hsel_verts : ∀ idx ∈ selIdxs,
    es[idx.val].u ∈ visitedSet ctx.auxBase n sLim mem ∧
    es[idx.val].v ∈ visitedSet ctx.auxBase n sLim mem
  /-- Selected edges form an acyclic forest. -/
  hacyclic : IsAcyclic ((selIdxs.map fun i => es[i.val]).map IndexedEdge.toWeighted)
  /-- Selected forest extends to a minimum spanning forest of `es`. -/
  hext : ∃ F_ext : List (WeightedEdge n ℕ),
    IsMinSpanningForest (es.map IndexedEdge.toWeighted)
      (((selIdxs.map fun i => es[i.val]).map IndexedEdge.toWeighted) ++ F_ext)
  /-- Buffer `selBuf` stores the original `id` of every selected edge. -/
  hsel_buf : ∀ j (hj : j < selIdxs.length),
    mem (ctx.selBufBase + selLen0 + j) = es[selIdxs[j].val].id
  /-- Supervertex labels of visited trees lie below `nComp`. -/
  hsup_range : ∀ v ∈ visitedSet ctx.auxBase n sLim mem,
    mem (ctx.auxBase + 2 * n + mem (ctx.auxBase + v.val)) < nComp
  /-- Supervertex equality on `visitedSet` characterizes `edgePartition` connectivity. -/
  hcomp_rel : ∀ x ∈ visitedSet ctx.auxBase n sLim mem,
    ∀ y ∈ visitedSet ctx.auxBase n sLim mem,
      mem (ctx.auxBase + 2 * n + mem (ctx.auxBase + x.val)) =
          mem (ctx.auxBase + 2 * n + mem (ctx.auxBase + y.val)) ↔
        (edgePartition ((selIdxs.map fun i => es[i.val]).map
          IndexedEdge.toWeighted)).rel x y = true
  /-- Each supervertex class is either a full connected component or has `≥ ctx.thresh + 1`
  external neighbors across `es`. -/
  hcomp_deg : ∀ c : Fin nComp,
    (∃ v ∈ visitedSet ctx.auxBase n sLim mem,
      mem (ctx.auxBase + 2 * n + mem (ctx.auxBase + v.val)) = c.val) ∧
    ((∀ e ∈ es,
        (e.u ∈ visitedSet ctx.auxBase n sLim mem ∧
          mem (ctx.auxBase + 2 * n + mem (ctx.auxBase + e.u.val)) = c.val) ↔
        (e.v ∈ visitedSet ctx.auxBase n sLim mem ∧
          mem (ctx.auxBase + 2 * n + mem (ctx.auxBase + e.v.val)) = c.val)) ∨
      ∃ A Z : Finset (Fin n),
        A ⊆ visitedSet ctx.auxBase n sLim mem ∧
        (∀ u ∈ A, mem (ctx.auxBase + 2 * n + mem (ctx.auxBase + u.val)) = c.val) ∧
        ctx.thresh + 1 ≤ Z.card ∧
        ∀ z ∈ Z, z ∉ A ∧ ∃ e ∈ es, (e.u ∈ A ∧ e.v = z) ∨ (e.v ∈ A ∧ e.u = z))

/-- `phasePot` initial sum bound: at `sLim = 0` (`tr[v] = n`),
`phasePot ≤ 8 * n + 234 * es.length + 130 * n + 92 * (n * ((2 * mRef) / n))`. -/
theorem phasePot_zero_le {n mRef : ℕ} {ctx : FTCtx} {es : List (IndexedEdge n)}
    {mem : ℕ → ℕ} (hcsr : HoldsUndirCSR ctx.offBase ctx.adjBase es mem) :
    phasePot ctx n mRef 0 mem ≤
      234 * es.length + 138 * n + 92 * (n * ((2 * mRef) / n)) := by
  dsimp only [phasePot, vertexPot]
  have hsum_deg : ∑ v : Fin n, (mem (ctx.offBase + v.val + 1) - mem (ctx.offBase + v.val)) =
      2 * es.length := holdsUndirCSR_sum_deg hcsr
  have hsplit : ∑ v : Fin n,
      (117 * (mem (ctx.offBase + v.val + 1) - mem (ctx.offBase + v.val)) +
        130 + 92 * ((2 * mRef) / n)) =
      117 * ∑ v : Fin n, (mem (ctx.offBase + v.val + 1) - mem (ctx.offBase + v.val)) +
        (130 * n + 92 * (n * ((2 * mRef) / n))) := by
    simp only [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin]
    ring
  have hite : ∑ v : Fin n,
      (if mem (ctx.auxBase + v.val) < 0 then 0
       else 117 * (mem (ctx.offBase + v.val + 1) - mem (ctx.offBase + v.val)) +
         130 + 92 * ((2 * mRef) / n)) ≤
      ∑ v : Fin n,
        (117 * (mem (ctx.offBase + v.val + 1) - mem (ctx.offBase + v.val)) +
          130 + 92 * ((2 * mRef) / n)) := by
    refine Finset.sum_le_sum fun v _ => ?_
    split_ifs <;> omega
  rw [hsplit, hsum_deg] at hite
  omega

end Cslib.Algorithms.WordRAM.MinimumSpanningForest.DenseCase
