/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.GraphOps.Dedup
public import CslibFrontier.Algorithms.Lean.Kruskal.Basic
import CslibFrontier.Computability.WordRAM.Realization.LoopFrame

/-!
# Tests for WordRAM Edge Deduplication (`GraphOps.Dedup`)

Kernel-checked tests exercising `dedupSimpleEdgesProg_spec`, `realizes_dedupSimpleEdgesProg`, and
`isMinSpanningForest_of_dedupSimpleEdges` on:
* parallel duplicate edges (including tie-breaking and reversed endpoints) mixed with self-loops,
* empty and all-self-loop graphs.
-/

public section

namespace CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.GraphOpsDedup

open Cslib.Algorithms.Lean.Kruskal
open Cslib.Algorithms.WordRAM.MinimumSpanningForest
open Cslib.DataStructure
open Cslib.Query.MinimumSpanningForest
open Cslib.WordRAM
open Cslib.WordRAM.Realization

/-- Word projection of a stride-4 `IndexedEdge` (`0 ↦ u`, `1 ↦ v`, `2 ↦ weight`, `3 ↦ id`). -/
@[expose] def edgeWord {n : ℕ} (e : IndexedEdge n) : ℕ → ℕ
  | 0 => e.u.val
  | 1 => e.v.val
  | 2 => e.weight
  | _ => e.id

private theorem edgeWord_fits {w n : ℕ} {e : IndexedEdge n}
    (hu : Fits w e.u.val) (hv : Fits w e.v.val) (hw : Fits w e.weight) (hid : Fits w e.id) :
    ∀ q, Fits w (edgeWord e q)
  | 0 => hu
  | 1 => hv
  | 2 => hw
  | _ + 3 => hid

/-- Memory image laying out `es` contiguously at `[base, base + 4 * es.length)` over `bg`. -/
@[expose] def edgeArrayMem {n : ℕ} (base : ℕ) (es : List (IndexedEdge n)) (bg : ℕ → ℕ)
    (a : ℕ) : ℕ :=
  if h : base ≤ a ∧ a < base + 4 * es.length then
    let off := a - base
    edgeWord (es[off / 4]'(by omega)) (off % 4)
  else bg a

private theorem holdsIndexedEdges_edgeArrayMem {n : ℕ} (base : ℕ) (es : List (IndexedEdge n))
    (bg : ℕ → ℕ) : HoldsIndexedEdges base es (edgeArrayMem base es bg) := by
  intro i hi
  have hmem : ∀ q < 4, edgeArrayMem base es bg (base + 4 * i + q) = edgeWord es[i] q := by
    intro q hq
    have hlt : base ≤ base + 4 * i + q ∧ base + 4 * i + q < base + 4 * es.length := by omega
    dsimp only [edgeArrayMem]
    split_ifs
    have hdiv : (base + 4 * i + q - base) / 4 = i := by omega
    have hmod : (base + 4 * i + q - base) % 4 = q := by omega
    simp only [hdiv, hmod]
  exact ⟨hmem 0 (by decide), hmem 1 (by decide), hmem 2 (by decide), hmem 3 (by decide)⟩

private theorem wellFormed_edgeArrayMem {w n base front : ℕ} (es : List (IndexedEdge n))
    (bg : ℕ → ℕ) (hfront : Fits w front) (hbg : ∀ a, Fits w (bg a))
    (hes : ∀ e ∈ es, Fits w e.u.val ∧ Fits w e.v.val ∧ Fits w e.weight ∧ Fits w e.id) :
    Memory.WellFormed w ⟨edgeArrayMem base es bg, front⟩ := by
  refine ⟨hfront, fun a => ?_⟩
  dsimp only [edgeArrayMem]
  split_ifs with h
  · obtain ⟨hu, hv, hw, hid⟩ := hes (es[(a - base) / 4]'(by omega)) (List.getElem_mem _)
    exact edgeWord_fits hu hv hw hid _
  · exact hbg a

private theorem edgeArrayMem_lt {n base : ℕ} (es : List (IndexedEdge n)) (bg : ℕ → ℕ)
    {a : ℕ} (ha : a < base) : edgeArrayMem base es bg a = bg a := by
  dsimp only [edgeArrayMem]
  split_ifs with h
  · omega
  · rfl

private theorem kruskalEdges_nil (n : ℕ) :
    kruskalEdges ([] : List (WeightedEdge n ℕ)) = [] := by
  simp [kruskalEdges, sortEdges, List.mergeSort_nil]

/-- Sample 4-vertex multigraph with self-loops, parallel edges, reversed endpoints, and ties. -/
@[expose] def sampleEdges : List (IndexedEdge 4) :=
  [⟨2, 2, 1, 10⟩, ⟨1, 0, 5, 11⟩, ⟨0, 1, 3, 12⟩, ⟨1, 0, 3, 13⟩,
   ⟨1, 2, 2, 14⟩, ⟨0, 0, 0, 15⟩, ⟨2, 0, 4, 16⟩]

/-- Expected canonical `dedupSimpleEdges` output on `sampleEdges`. -/
@[expose] def sampleDedupExpected : List (WeightedEdge 4 ℕ) :=
  [⟨0, 1, 3⟩, ⟨2, 0, 4⟩, ⟨1, 2, 2⟩]

private theorem sampleEdges_dedup_eq :
    dedupSimpleEdges (sampleEdges.map IndexedEdge.toWeighted) = sampleDedupExpected := by
  decide

example :
    let s : Memory.State := ⟨edgeArrayMem 4 sampleEdges (fun _ => 77), 32⟩
    let prog := dedupSimpleEdgesProg ⟨4, sampleEdges.length, 4⟩
    let out := (Memory.spec 0).clientResult s prog
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s ≤ 41 * sampleEdges.length + 6 * 4 + 6 ∧
    out.numVertices = 4 ∧
    out.numEdges = 3 ∧
    out.edgeBase + 4 * out.numEdges ≤ s'.frontier ∧
    s'.frontier ≤ 32 + (13 * sampleEdges.length + 2 * 4) ∧
    s'.mem 0 = 77 ∧
    ∃ esOut : List (IndexedEdge 4),
      esOut.length = 3 ∧
      esOut = [⟨0, 1, 3, 12⟩, ⟨2, 0, 4, 16⟩, ⟨1, 2, 2, 14⟩] ∧
      esOut.Subperm sampleEdges ∧
      HoldsIndexedEdges out.edgeBase esOut s'.mem ∧
      esOut.map IndexedEdge.toWeighted = sampleDedupExpected ∧
      IsSimple (edgeEnds (esOut.map IndexedEdge.toWeighted)) ∧
      IsMinSpanningForest (sampleEdges.map IndexedEdge.toWeighted)
        (kruskalEdges (esOut.map IndexedEdge.toWeighted)) := by
  have h16 : Fits 16 16 := by decide
  have hwf : Memory.WellFormed 16 ⟨edgeArrayMem 4 sampleEdges (fun _ => 77), 32⟩ := by
    refine wellFormed_edgeArrayMem sampleEdges (fun _ => 77) (by decide)
      (fun _ => by decide) ?_
    intro e he
    simp only [sampleEdges, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨by decide, by decide, by decide, by decide⟩
  have hft := dedupSimpleEdgesProg_spec h16 hwf
    (holdsIndexedEdges_edgeArrayMem 4 sampleEdges (fun _ => 77))
    (by decide) (by decide)
  obtain ⟨_, hcost, hmod, hvn, heb, hs'fr, _, esOut, hlen, hsub, hholds, hded, hsimp, _⟩ :=
    framedTriple_iff_realization.mp hft
  have hded' : esOut.map IndexedEdge.toWeighted = sampleDedupExpected :=
    hded.trans sampleEdges_dedup_eq
  have hlen3 : esOut.length = 3 := by
    have h1 := congrArg List.length hded'
    simpa [sampleDedupExpected] using h1
  have hes_eq : esOut = [⟨0, 1, 3, 12⟩, ⟨2, 0, 4, 16⟩, ⟨1, 2, 2, 14⟩] := by
    rcases esOut with _ | ⟨e0, _ | ⟨e1, _ | ⟨e2, _ | _⟩⟩⟩ <;>
      simp only [sampleDedupExpected, List.map_nil, List.map_cons, List.cons.injEq,
        and_false, reduceCtorEq] at hded'
    rcases hded' with ⟨hw0, hw1, hw2, _⟩
    have hm0 : e0 ∈ sampleEdges := hsub.subset (by simp)
    have hm1 : e1 ∈ sampleEdges := hsub.subset (by simp)
    have hm2 : e2 ∈ sampleEdges := hsub.subset (by simp)
    simp only [sampleEdges, List.mem_cons, List.not_mem_nil, or_false] at hm0 hm1 hm2
    have h0 : e0 = ⟨0, 1, 3, 12⟩ := by
      rcases hm0 with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | rfl | exact absurd hw0 (by decide)
    have h1 : e1 = ⟨2, 0, 4, 16⟩ := by
      rcases hm1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | rfl | exact absurd hw1 (by decide)
    have h2 : e2 = ⟨1, 2, 2, 14⟩ := by
      rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | rfl | exact absurd hw2 (by decide)
    subst h0 h1 h2
    rfl
  have hmsf : IsMinSpanningForest (sampleEdges.map IndexedEdge.toWeighted)
      (kruskalEdges (esOut.map IndexedEdge.toWeighted)) :=
    isMinSpanningForest_of_dedupSimpleEdges _ _ (hded ▸ kruskalEdges_isMinSpanningForest _)
  have hmem0_step : ((Memory.spec 0).clientState ⟨edgeArrayMem 4 sampleEdges (fun _ => 77), 32⟩
      (dedupSimpleEdgesProg ⟨4, sampleEdges.length, 4⟩)).mem 0 =
      edgeArrayMem 4 sampleEdges (fun _ => 77) 0 :=
    hmod.mem_eq_of_not_mem (by decide) (Set.notMem_empty 0)
  have hmem0 : ((Memory.spec 0).clientState ⟨edgeArrayMem 4 sampleEdges (fun _ => 77), 32⟩
      (dedupSimpleEdgesProg ⟨4, sampleEdges.length, 4⟩)).mem 0 = 77 :=
    hmem0_step.trans (edgeArrayMem_lt sampleEdges (fun _ => 77) (by decide))
  refine ⟨by simpa using hcost, hvn, hlen.symm.trans hlen3, heb, hs'fr, hmem0, esOut, hlen3,
    hes_eq, hsub, hholds, hded', hsimp, hmsf⟩

example :
    let s : Memory.State := ⟨edgeArrayMem 4 sampleEdges (fun _ => 77), 32⟩
    let g : GraphSlice := ⟨4, sampleEdges.length, 4⟩
    Fits 16 16 ∧ g.edgeBase + 4 * g.numEdges ≤ s.frontier ∧
      Fits 16 (s.frontier + (13 * g.numEdges + 2 * g.numVertices)) ∧
      (∀ j < g.numEdges,
        s.mem (g.edgeBase + 4 * j) < g.numVertices ∧
        s.mem (g.edgeBase + 4 * j + 1) < g.numVertices) ∧
      Realizes .exact dedupSimpleEdgesProg WordEncoding.encode WordEncoding.encode
        (fun w g s => Fits w 16 ∧ g.edgeBase + 4 * g.numEdges ≤ s.frontier ∧
          Fits w (s.frontier + (13 * g.numEdges + 2 * g.numVertices)) ∧
          ∀ j < g.numEdges,
            s.mem (g.edgeBase + 4 * j) < g.numVertices ∧
            s.mem (g.edgeBase + 4 * j + 1) < g.numVertices)
        (fun _ _ => 0) := by
  refine ⟨by decide, by decide, by decide, fun j hj => ?_, realizes_dedupSimpleEdgesProg⟩
  have hholds := holdsIndexedEdges_edgeArrayMem 4 sampleEdges (fun _ => 77) j hj
  dsimp only
  rw [hholds.1, hholds.2.1]
  exact ⟨sampleEdges[j].u.isLt, sampleEdges[j].v.isLt⟩

example :
    let es : List (IndexedEdge 3) := []
    let s : Memory.State := ⟨fun _ => 0, 4⟩
    let prog := dedupSimpleEdgesProg ⟨3, 0, 4⟩
    let out := (Memory.spec 0).clientResult s prog
    let s' := (Memory.spec 0).clientState s prog
    out.numEdges = 0 ∧
    ∃ esOut : List (IndexedEdge 3),
      esOut = [] ∧
      HoldsIndexedEdges out.edgeBase esOut s'.mem ∧
      IsSimple (edgeEnds (esOut.map IndexedEdge.toWeighted)) ∧
      IsMinSpanningForest (es.map IndexedEdge.toWeighted) [] := by
  have hwf : Memory.WellFormed 8 ⟨fun _ => 0, 4⟩ := ⟨by decide, fun _ => by dsimp only; decide⟩
  have hft := dedupSimpleEdgesProg_spec (w := 8) (n := 3) (edgeBase := 4) (es := [])
    (by decide) hwf (fun _ hi => absurd hi (Nat.not_lt_zero _)) (by decide) (by decide)
  obtain ⟨_, _, _, _, _, _, _, esOut, hlen, hsub, hholds, _, hsimp, _⟩ :=
    framedTriple_iff_realization.mp hft
  have hnil : esOut = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hsub.length_le)
  subst hnil
  have hmsf : IsMinSpanningForest (([] : List (IndexedEdge 3)).map IndexedEdge.toWeighted) [] := by
    rw [← kruskalEdges_nil 3]
    exact kruskalEdges_isMinSpanningForest _
  exact ⟨hlen.symm, [], rfl, hholds, hsimp, hmsf⟩

/-- All-self-loop fixture verifying empty simple output and `IsMinSpanningForest` lifting. -/
@[expose] def selfLoopEdges : List (IndexedEdge 3) :=
  [⟨1, 1, 5, 0⟩, ⟨0, 0, 2, 1⟩, ⟨2, 2, 9, 2⟩]

example :
    let s : Memory.State := ⟨edgeArrayMem 4 selfLoopEdges (fun _ => 55), 16⟩
    let prog := dedupSimpleEdgesProg ⟨3, selfLoopEdges.length, 4⟩
    let out := (Memory.spec 0).clientResult s prog
    let s' := (Memory.spec 0).clientState s prog
    out.numEdges = 0 ∧
    s'.mem 0 = 55 ∧
    ∃ esOut : List (IndexedEdge 3),
      esOut = [] ∧
      IsSimple (edgeEnds (esOut.map IndexedEdge.toWeighted)) ∧
      IsMinSpanningForest (selfLoopEdges.map IndexedEdge.toWeighted) [] := by
  have hwf : Memory.WellFormed 16 ⟨edgeArrayMem 4 selfLoopEdges (fun _ => 55), 16⟩ := by
    refine wellFormed_edgeArrayMem selfLoopEdges (fun _ => 55) (by decide)
      (fun _ => by decide) ?_
    intro e he
    simp only [selfLoopEdges, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;> exact ⟨by decide, by decide, by decide, by decide⟩
  have hft := dedupSimpleEdgesProg_spec (w := 16) (n := 3) (edgeBase := 4) (es := selfLoopEdges)
    (by decide) hwf (holdsIndexedEdges_edgeArrayMem 4 selfLoopEdges (fun _ => 55))
    (by decide) (by decide)
  obtain ⟨_, _, hmod, _, _, _, _, esOut, hlen, _, _, hded, hsimp, _⟩ :=
    framedTriple_iff_realization.mp hft
  have hded_nil : dedupSimpleEdges (selfLoopEdges.map IndexedEdge.toWeighted) = [] := by decide
  have hded_eq : esOut.map IndexedEdge.toWeighted = [] := hded.trans hded_nil
  have hnil : esOut = [] := List.map_eq_nil_iff.mp hded_eq
  subst hnil
  have hmem0_step : ((Memory.spec 0).clientState ⟨edgeArrayMem 4 selfLoopEdges (fun _ => 55), 16⟩
      (dedupSimpleEdgesProg ⟨3, selfLoopEdges.length, 4⟩)).mem 0 =
      edgeArrayMem 4 selfLoopEdges (fun _ => 55) 0 :=
    hmod.mem_eq_of_not_mem (by decide) (Set.notMem_empty 0)
  have hmem0 : ((Memory.spec 0).clientState ⟨edgeArrayMem 4 selfLoopEdges (fun _ => 55), 16⟩
      (dedupSimpleEdgesProg ⟨3, selfLoopEdges.length, 4⟩)).mem 0 = 55 :=
    hmem0_step.trans (edgeArrayMem_lt selfLoopEdges (fun _ => 55) (by decide))
  have hmsf :
      IsMinSpanningForest (([] : List (IndexedEdge 3)).map IndexedEdge.toWeighted) [] := by
    rw [← kruskalEdges_nil 3]
    exact kruskalEdges_isMinSpanningForest _
  exact ⟨hlen.symm, hmem0, [], rfl, hsimp,
    isMinSpanningForest_of_dedupSimpleEdges _ _ (hded ▸ hmsf)⟩

end CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.GraphOpsDedup
