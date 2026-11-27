/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.GraphOps.Components
import CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.GraphOpsTestSupport
import CslibFrontier.Tactic.Fits
import CslibFrontier.Tactic.Realize

/-!
# Tests for Word-RAM Minimum Spanning Forest Component Operations

Exercises the public `*_spec`, `realizes_*`, and graph-theory bridge interfaces of
`connectedComponentsProg`, `contractEdgesProg`, and `compactVerticesProg` under `module`
encapsulation on disconnected components, isolated vertices, `m = 0` and multigraph (`m > n`,
self-loop, parallel edges, cycle, isolated vertex) boundaries, and an end-to-end `realize`
pipeline.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.GraphOpsComponents

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.Algorithms.Lean.Kruskal
open Cslib.Query.MinimumSpanningForest
open Cslib.Algorithms.WordRAM.MinimumSpanningForest
open CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.GraphOpsTestSupport

/-! ## `Components`: BFS Component Count, Edge Contraction, and Vertex Compaction -/

-- `connectedComponentsProg` on `disconnEdges` (`{0,1,2}`, `{3,4}`, `{5}`): `numComps = 3`.
example :
    let disconnEdges : List (IndexedEdge 6) :=
      [⟨⟨0, by decide⟩, ⟨1, by decide⟩, 3, 100⟩,
       ⟨⟨1, by decide⟩, ⟨2, by decide⟩, 4, 101⟩,
       ⟨⟨3, by decide⟩, ⟨4, by decide⟩, 2, 102⟩]
    let s0 := mkInitState disconnEdges
    let g : GraphSlice := ⟨6, 3, 0⟩
    let r := execWordRAM s0 (connectedComponentsProg g)
    r.1.compBase = 37 ∧ r.1.numComps = 3 ∧ r.2.1.frontier = 49 ∧
    r.2.2 ≤ 24 * 3 + 13 * 6 + 8 ∧
    (Memory.spec 16).ValidHistory s0
      ((Memory.spec 16).clientHistory s0 (connectedComponentsProg g)) ∧
    r.2.1.mem (r.1.compBase + 0) = r.2.1.mem (r.1.compBase + 1) ∧
    r.2.1.mem (r.1.compBase + 1) = r.2.1.mem (r.1.compBase + 2) ∧
    r.2.1.mem (r.1.compBase + 3) = r.2.1.mem (r.1.compBase + 4) ∧
    r.2.1.mem (r.1.compBase + 0) ≠ r.2.1.mem (r.1.compBase + 3) ∧
    r.2.1.mem (r.1.compBase + 0) ≠ r.2.1.mem (r.1.compBase + 5) ∧
    r.2.1.mem (r.1.compBase + 3) ≠ r.2.1.mem (r.1.compBase + 5) := by
  intro disconnEdges s0 g r
  dsimp only [r, s0, g, execWordRAM]
  have h16 : Fits 16 16 := by decide
  have hinit := mkInitState_spec (w := 16) disconnEdges (by decide) (by decide)
    (fun e he => by simp only [disconnEdges, List.mem_cons, List.not_mem_nil, or_false] at he
                    rcases he with rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩)
  have hft := connectedComponentsProg_spec h16 hinit.1 hinit.2.2 (by rw [hinit.2.1]; decide)
    (by rw [hinit.2.1]; decide)
  have hlen3 : disconnEdges.length = 3 := rfl
  rw [hlen3] at hft
  obtain ⟨hv, hcost, _, hcb, _, hfr, _, _, _, hconn, hnum⟩ := framedTriple_iff_realization.mp hft
  have hnum3 : (edgePartition (disconnEdges.map IndexedEdge.toWeighted)).numComponents = 3 := by
    decide
  refine ⟨by rw [hcb, hinit.2.1]; rfl, hnum.trans hnum3, by rw [hfr, hinit.2.1]; rfl,
    hcost, hv, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hconn ⟨0, by decide⟩ ⟨1, by decide⟩).mpr (by decide)
  · exact (hconn ⟨1, by decide⟩ ⟨2, by decide⟩).mpr (by decide)
  · exact (hconn ⟨3, by decide⟩ ⟨4, by decide⟩).mpr (by decide)
  · intro heq; exact absurd ((hconn ⟨0, by decide⟩ ⟨3, by decide⟩).mp heq) (by decide)
  · intro heq; exact absurd ((hconn ⟨0, by decide⟩ ⟨5, by decide⟩).mp heq) (by decide)
  · intro heq; exact absurd ((hconn ⟨3, by decide⟩ ⟨5, by decide⟩).mp heq) (by decide)

-- `connectedComponentsProg` on empty `m = 0` (`4` isolated vertices -> `4` components).
example :
    let s0 := mkInitState ([] : List (IndexedEdge 4))
    let g : GraphSlice := ⟨4, 0, 0⟩
    let r := execWordRAM s0 (connectedComponentsProg g)
    r.1.numComps = 4 ∧ r.2.1.frontier = 17 ∧
    (Memory.spec 16).ValidHistory s0
      ((Memory.spec 16).clientHistory s0 (connectedComponentsProg g)) ∧
    (∀ x y : Fin 4, r.2.1.mem (r.1.compBase + x.val) = r.2.1.mem (r.1.compBase + y.val) ↔
      x = y) := by
  intro s0 g r
  dsimp only [r, s0, g, execWordRAM]
  have h16 : Fits 16 16 := by decide
  have hinit := mkInitState_spec (w := 16) ([] : List (IndexedEdge 4))
    (by decide) (by decide) (fun _ h => by simp at h)
  have hft := connectedComponentsProg_spec h16 hinit.1 hinit.2.2 (by rw [hinit.2.1]; decide)
    (by rw [hinit.2.1]; decide)
  simp only [List.length_nil, Nat.mul_zero] at hft
  obtain ⟨hv, _, _, _, _, hfr, _, _, _, hconn, hnum⟩ := framedTriple_iff_realization.mp hft
  have hnum4 :
      (edgePartition (([] : List (IndexedEdge 4)).map IndexedEdge.toWeighted)).numComponents =
        4 := by decide
  refine ⟨hnum.trans hnum4, by rw [hfr, hinit.2.1]; rfl, hv, fun x y => ?_⟩
  rw [hconn x y]
  fin_cases x <;> fin_cases y <;> decide

-- `contractEdgesProg` on `disconnEdges` along `[0, 0, 0, 1, 1, 2]`.
example :
    let disconnEdges : List (IndexedEdge 6) :=
      [⟨⟨0, by decide⟩, ⟨1, by decide⟩, 3, 100⟩,
       ⟨⟨1, by decide⟩, ⟨2, by decide⟩, 4, 101⟩,
       ⟨⟨3, by decide⟩, ⟨4, by decide⟩, 2, 102⟩]
    let s0 := mkInitState disconnEdges
    let prog : Memory.Prog ℕ := do
      let compBase ← initFromWordsProg [0, 0, 0, 1, 1, 2]
      contractEdgesProg ⟨3, 0, compBase⟩
    let r := execWordRAM s0 prog
    r.1 = 18 ∧ r.2.1.frontier = 30 ∧ r.2.2 ≤ 38 ∧
    (Memory.spec 16).ValidHistory s0 ((Memory.spec 16).clientHistory s0 prog) ∧
    readIndexedEdges r.1 3 r.2.1.mem = [(0, 0, 3, 100), (0, 0, 4, 101), (1, 1, 2, 102)] := by
  intro disconnEdges s0 prog r
  dsimp only [r, execWordRAM]
  have h16 : Fits 16 16 := by decide
  have hinit := mkInitState_spec (w := 16) disconnEdges (by decide) (by decide)
    (fun e he => by simp only [disconnEdges, List.mem_cons, List.not_mem_nil, or_false] at he
                    rcases he with rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩)
  have hcomp_ft := initFromWordsProg_spec (words := [0, 0, 0, 1, 1, 2])
    hinit.1 (by rw [hinit.2.1]; decide)
    (fun v hv => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
                    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  let compFn : Fin 6 → ℕ := fun u => [0, 0, 0, 1, 1, 2][u.val]!
  have hft : Memory.FramedTriple 16 s0 prog 38 ∅ fun out s' =>
      out = 18 ∧ s'.frontier = 30 ∧
      ∃ esOut : List (IndexedEdge 3),
        esOut.length = 3 ∧ HoldsIndexedEdges out esOut s'.mem ∧
        (∀ i (hi : i < 3) (hi' : i < esOut.length),
          (esOut[i]'hi').u.val = compFn (disconnEdges[i]'hi).u ∧
          (esOut[i]'hi').v.val = compFn (disconnEdges[i]'hi).v ∧
          (esOut[i]'hi').weight = (disconnEdges[i]'hi).weight ∧
          (esOut[i]'hi').id = (disconnEdges[i]'hi).id) := by
    have hbind : Memory.FramedTriple 16 s0 prog
        ([0, 0, 0, 1, 1, 2].length + 1 + 31) ∅ fun out s' =>
        out = 18 ∧ s'.frontier = 30 ∧
        ∃ esOut : List (IndexedEdge 3),
          esOut.length = 3 ∧ HoldsIndexedEdges out esOut s'.mem ∧
          (∀ i (hi : i < 3) (hi' : i < esOut.length),
            (esOut[i]'hi').u.val = compFn (disconnEdges[i]'hi).u ∧
            (esOut[i]'hi').v.val = compFn (disconnEdges[i]'hi).v ∧
            (esOut[i]'hi').weight = (disconnEdges[i]'hi).weight ∧
            (esOut[i]'hi').id = (disconnEdges[i]'hi).id) := by
      refine Memory.FramedTriple.bind_same
        (Memory.Triple.mono hcomp_ft le_rfl fun compB t ⟨hm, hb, hfr, hhold, hwf'⟩ => ?_)
      refine ⟨hm, ?_⟩
      have hin' : HoldsIndexedEdges 0 disconnEdges t.mem :=
        hinit.2.2.congr fun a _ ha => hm.mem_eq_of_not_mem (by rw [hinit.2.1]; omega)
          (Set.notMem_empty _)
      have hcomp_mem : ∀ u : Fin 6, t.mem (compB + u.val) = compFn u := by
        obtain ⟨h0, h1⟩ := Block.holdsList_cons_iff.mp hhold
        obtain ⟨hv1, h2⟩ := Block.holdsList_cons_iff.mp h1
        obtain ⟨hv2, h3⟩ := Block.holdsList_cons_iff.mp h2
        obtain ⟨hv3, h4⟩ := Block.holdsList_cons_iff.mp h3
        obtain ⟨hv4, h5⟩ := Block.holdsList_cons_iff.mp h4
        obtain ⟨hv5, _⟩ := Block.holdsList_cons_iff.mp h5
        intro u
        fin_cases u
        · exact h0
        · exact hv1
        · exact hv2
        · exact hv3
        · exact hv4
        · exact hv5
      have hcomp_lt : ∀ e ∈ disconnEdges, compFn e.u < 3 ∧ compFn e.v < 3 := by
        intro e he
        simp only [disconnEdges, List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩
      have hdisLen : disconnEdges.length = 3 := rfl
      have hcon := contractEdgesProg_spec (edgeBase := 0) (compBase := compB) (n' := 3)
        h16 hwf' hin'
        (by rw [hfr, hinit.2.1, hdisLen]; omega)
        hcomp_mem
        (by
          rw [hb, hfr, hinit.2.1, hdisLen]
          simp only [List.length_cons, List.length_nil]
          omega)
        hcomp_lt
        (by rw [hfr, hinit.2.1, hdisLen]; decide)
      refine Memory.Triple.mono hcon (by rw [hdisLen])
        fun out s' ⟨hm2, hout, hfr2, _, esOut, hlen, hedges, hel⟩ => ?_
      refine ⟨hm2, by rw [hout, hfr, hinit.2.1, hdisLen]; rfl, ?_, esOut, hlen, hedges, hel⟩
      rw [hfr2, hfr, hinit.2.1, hdisLen]
      simp only [List.length_cons, List.length_nil]
    exact hbind.mono (by decide) fun _ _ hq => hq
  obtain ⟨hv, hcost, _, hout, hfr, esOut, hlen, hedges, hel⟩ :=
    framedTriple_iff_realization.mp hft
  have hdec : readIndexedEdges r.1 3 r.2.1.mem =
      [(0, 0, 3, 100), (0, 0, 4, 101), (1, 1, 2, 102)] := by
    dsimp only [r, execWordRAM]
    have h0' : 0 < esOut.length := by omega
    have h1' : 1 < esOut.length := by omega
    have h2' : 2 < esOut.length := by omega
    rcases hedges 0 h0' with ⟨m0u, m0v, m0w, m0i⟩
    rcases hedges 1 h1' with ⟨m1u, m1v, m1w, m1i⟩
    rcases hedges 2 h2' with ⟨m2u, m2v, m2w, m2i⟩
    rcases hel 0 (by decide) h0' with ⟨e0u, e0v, e0w, e0i⟩
    rcases hel 1 (by decide) h1' with ⟨e1u, e1v, e1w, e1i⟩
    rcases hel 2 (by decide) h2' with ⟨e2u, e2v, e2w, e2i⟩
    simp only [readIndexedEdges, List.range_succ, List.range_zero, List.nil_append,
      List.map_append, List.map_cons, List.map_nil]
    rw [m0u, m0v, m0w, m0i, m1u, m1v, m1w, m1i, m2u, m2v, m2w, m2i,
      e0u, e0v, e0w, e0i, e1u, e1v, e1w, e1i, e2u, e2v, e2w, e2i]
    rfl
  exact ⟨hout, hfr, hcost, hv, hdec⟩

-- `compactVerticesProg` on `isolatedEdges` (`6` vertices, isolated `0, 2, 3`):
-- `numVertices = 3`, simplicity, concrete `L_out` MSF, lifted MSF, and cost bound.
example :
    let isolatedEdges : List (IndexedEdge 6) :=
      [⟨⟨1, by decide⟩, ⟨4, by decide⟩, 7, 10⟩,
       ⟨⟨4, by decide⟩, ⟨5, by decide⟩, 2, 20⟩]
    let s0 := mkInitState isolatedEdges
    let g : GraphSlice := ⟨6, 2, 0⟩
    let r := execWordRAM s0 (compactVerticesProg g)
    r.1.numVertices = 3 ∧ r.1.liftBase = 8 ∧ r.1.edgeBase = 14 ∧ r.2.1.frontier = 22 ∧
    r.2.2 ≤ 14 * 2 + 3 * 6 + 2 ∧
    (Memory.spec 16).ValidHistory s0 ((Memory.spec 16).clientHistory s0 (compactVerticesProg g)) ∧
    ∃ (lift : Fin r.1.numVertices → Fin 6) (esOut : List (IndexedEdge r.1.numVertices))
        (L_out : List (WeightedEdge r.1.numVertices ℕ)),
      esOut.map (fun e => ⟨lift e.u, lift e.v, e.weight, e.id⟩) = isolatedEdges ∧
      IsSimple (edgeEnds (esOut.map IndexedEdge.toWeighted)) ∧
      IsMinSpanningForest (esOut.map IndexedEdge.toWeighted) L_out ∧
      IsMinSpanningForest (isolatedEdges.map IndexedEdge.toWeighted)
        (contractEdgeList lift L_out) ∧
      contractEdgeList lift L_out =
        [⟨⟨4, by decide⟩, ⟨5, by decide⟩, 2⟩, ⟨⟨1, by decide⟩, ⟨4, by decide⟩, 7⟩] := by
  intro isolatedEdges s0 g r
  dsimp only [r, s0, g, execWordRAM]
  have h16 : Fits 16 16 := by decide
  have hinit := mkInitState_spec (w := 16) isolatedEdges (by decide) (by decide)
    (fun e he => by simp only [isolatedEdges, List.mem_cons, List.not_mem_nil, or_false] at he
                    rcases he with rfl | rfl <;> exact ⟨by decide, by decide⟩)
  have hft := compactVerticesProg_spec h16 hinit.1 hinit.2.2 (by rw [hinit.2.1]; decide)
    (by rw [hinit.2.1]; decide)
  have hlen2 : isolatedEdges.length = 2 := rfl
  rw [hlen2] at hft
  obtain ⟨hv, hcost, _, hlift, hedge, _, hfr, _, lift, esOut, hinj, hlen, _, _, hact, hmap⟩ :=
    framedTriple_iff_realization.mp hft
  have hlen0 : 0 < esOut.length := by omega
  have hlen1 : 1 < esOut.length := by omega
  have h0_eq : (⟨lift (esOut[0]'hlen0).u, lift (esOut[0]'hlen0).v,
      (esOut[0]'hlen0).weight, (esOut[0]'hlen0).id⟩ :
      IndexedEdge 6) = isolatedEdges[0] := by
    have := congrArg (fun l => l[0]?) hmap
    simp only [List.getElem?_map, List.getElem?_eq_getElem hlen0,
      List.getElem?_eq_getElem (by decide : 0 < isolatedEdges.length),
      Option.map_some, Option.some.injEq] at this
    exact this
  have h1_eq : (⟨lift (esOut[1]'hlen1).u, lift (esOut[1]'hlen1).v,
      (esOut[1]'hlen1).weight, (esOut[1]'hlen1).id⟩ :
      IndexedEdge 6) = isolatedEdges[1] := by
    have := congrArg (fun l => l[1]?) hmap
    simp only [List.getElem?_map, List.getElem?_eq_getElem hlen1,
      List.getElem?_eq_getElem (by decide : 1 < isolatedEdges.length),
      Option.map_some, Option.some.injEq] at this
    exact this
  have hnv : r.1.numVertices = 3 := by
    dsimp only [r, s0, g, execWordRAM]
    let S : Finset (Fin 6) := {⟨1, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩}
    have hScard : S.card = 3 := by decide
    have himg : Finset.univ.image lift = S := by
      ext x
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨y, rfl⟩
        obtain ⟨e, he, hy⟩ := hact y
        have he' :
            (⟨lift e.u, lift e.v, e.weight, e.id⟩ : IndexedEdge 6) ∈ isolatedEdges := by
          have hmem := List.mem_map_of_mem
            (f := fun e => (⟨lift e.u, lift e.v, e.weight, e.id⟩ : IndexedEdge 6)) he
          rw [hmap] at hmem
          exact hmem
        simp only [isolatedEdges, List.mem_cons, List.not_mem_nil, or_false] at he'
        rcases he' with h0 | h1
        · rcases hy with rfl | rfl
          · have : lift e.u = ⟨1, by decide⟩ := congrArg IndexedEdge.u h0
            rw [this]; simp [S]
          · have : lift e.v = ⟨4, by decide⟩ := congrArg IndexedEdge.v h0
            rw [this]; simp [S]
        · rcases hy with rfl | rfl
          · have : lift e.u = ⟨4, by decide⟩ := congrArg IndexedEdge.u h1
            rw [this]; simp [S]
          · have : lift e.v = ⟨5, by decide⟩ := congrArg IndexedEdge.v h1
            rw [this]; simp [S]
      · intro hx
        simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact ⟨_, congrArg IndexedEdge.u h0_eq⟩
        · exact ⟨_, congrArg IndexedEdge.v h0_eq⟩
        · exact ⟨_, congrArg IndexedEdge.v h1_eq⟩
    have hcard := (Finset.card_image_of_injective Finset.univ hinj).trans (Finset.card_fin _)
    exact hcard.symm.trans ((congrArg Finset.card himg).trans hScard)
  have hsimp_out : IsSimple (edgeEnds (esOut.map IndexedEdge.toWeighted)) := by
    refine compactVertices_isSimple hmap ?_
    rw [isSimple_iff]
    refine ⟨fun i => by fin_cases i <;> decide, fun i₁ i₂ h => ?_⟩
    fin_cases i₁ <;> fin_cases i₂ <;>
      simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.zero_eq_one_iff,
        Fin.one_eq_zero_iff, Fin.reduceFinMk, List.map_cons, List.map_nil, List.length_cons,
        List.length_nil, zero_add, Nat.reduceAdd, OfNat.ofNat_ne_one] at h ⊢
    all_goals revert h; decide
  let e0 := esOut[0]'hlen0
  let e1 := esOut[1]'hlen1
  let L_out : List (WeightedEdge _ ℕ) := [e1.toWeighted, e0.toWeighted]
  have hesOut_eq : esOut = [e0, e1] := by
    refine List.ext_getElem (by simp [hlen]) fun i hi₁ hi₂ => ?_
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;> rfl
  have he0u : lift e0.u = ⟨1, by decide⟩ := congrArg IndexedEdge.u h0_eq
  have he0v : lift e0.v = ⟨4, by decide⟩ := congrArg IndexedEdge.v h0_eq
  have hw0 : e0.weight = 7 := congrArg IndexedEdge.weight h0_eq
  have he1u : lift e1.u = ⟨4, by decide⟩ := congrArg IndexedEdge.u h1_eq
  have he1v : lift e1.v = ⟨5, by decide⟩ := congrArg IndexedEdge.v h1_eq
  have hw1 : e1.weight = 2 := congrArg IndexedEdge.weight h1_eq
  have hperm_out : L_out.Perm (esOut.map IndexedEdge.toWeighted) := by
    rw [hesOut_eq, List.map_cons, List.map_cons, List.map_nil]
    exact List.Perm.swap e0.toWeighted e1.toWeighted []
  have h1_rel : (DisjointSet.Partition.discrete _).rel e1.u e1.v = false :=
    Bool.eq_false_iff.mpr fun h => by
      have := congrArg lift (DisjointSet.Partition.rel_discrete_eq_true.mp h)
      rw [he1u, he1v] at this; revert this; decide
  have h0_rel : ((DisjointSet.Partition.discrete _).merge e1.u e1.v).rel e0.u e0.v = false :=
    Bool.eq_false_iff.mpr fun h => by
      rcases DisjointSet.Partition.rel_merge_eq_true.mp h with hxy | ⟨hxa, _⟩ | ⟨hxb, _⟩
      · have := congrArg lift (DisjointSet.Partition.rel_discrete_eq_true.mp hxy)
        rw [he0u, he0v] at this; revert this; decide
      · have := congrArg lift (DisjointSet.Partition.rel_discrete_eq_true.mp hxa)
        rw [he0u, he1u] at this; revert this; decide
      · have := congrArg lift (DisjointSet.Partition.rel_discrete_eq_true.mp hxb)
        rw [he0u, he1v] at this; revert this; decide
  have hmsf_out : IsMinSpanningForest (esOut.map IndexedEdge.toWeighted) L_out := by
    rw [isMinSpanningForest_iff_threshold_partition]
    refine ⟨⟨hperm_out.subperm, ?_, Perm.edgePartition_eq hperm_out⟩,
      fun t => Perm.edgePartition_eq (hperm_out.filter _)⟩
    exact isAcyclicFrom_cons.mpr ⟨h1_rel, isAcyclicFrom_cons.mpr ⟨h0_rel, isAcyclicFrom_nil _⟩⟩
  have hmsf_lift : IsMinSpanningForest (isolatedEdges.map IndexedEdge.toWeighted)
      (contractEdgeList lift L_out) :=
    compactVertices_isMinSpanningForest hinj hmap hmsf_out
  have hcon_eq : contractEdgeList lift L_out =
      [⟨⟨4, by decide⟩, ⟨5, by decide⟩, 2⟩, ⟨⟨1, by decide⟩, ⟨4, by decide⟩, 7⟩] := by
    simp [L_out, contractEdgeList, contractEdge, IndexedEdge.toWeighted,
      he0u, he0v, hw0, he1u, he1v, hw1]
  exact ⟨hnv, by rw [hlift, hinit.2.1]; rfl, by rw [hedge, hinit.2.1]; rfl,
    by rw [hfr, hinit.2.1]; rfl, hcost, hv,
    ⟨lift, esOut, L_out, hmap, hsimp_out, hmsf_out, hmsf_lift, hcon_eq⟩⟩

-- `compactVerticesProg` on empty `m = 0` (`4` isolated vertices -> `0` active vertices).
example :
    let s0 := mkInitState ([] : List (IndexedEdge 4))
    let g : GraphSlice := ⟨4, 0, 0⟩
    let r := execWordRAM s0 (compactVerticesProg g)
    r.1.numVertices = 0 ∧ r.2.1.frontier = 4 ∧ r.2.2 ≤ 3 * 4 + 2 ∧
    (Memory.spec 16).ValidHistory s0
      ((Memory.spec 16).clientHistory s0 (compactVerticesProg g)) := by
  intro s0 g r
  dsimp only [r, s0, g, execWordRAM]
  have h16 : Fits 16 16 := by decide
  have hinit := mkInitState_spec (w := 16) ([] : List (IndexedEdge 4))
    (by decide) (by decide) (fun _ h => by simp at h)
  have hft := compactVerticesProg_spec h16 hinit.1 hinit.2.2 (by rw [hinit.2.1]; decide)
    (by rw [hinit.2.1]; decide)
  simp only [List.length_nil, Nat.mul_zero] at hft
  obtain ⟨hv, hcost, _, _, _, _, hfr, _, _, esOut, _, hlen, _, _, hact, _⟩ :=
    framedTriple_iff_realization.mp hft
  have hnv0 : r.1.numVertices = 0 := by
    dsimp only [r, s0, g, execWordRAM]
    by_contra hne
    have hpos : 0 < r.1.numVertices := Nat.pos_of_ne_zero hne
    obtain ⟨e, he, _⟩ := hact ⟨0, hpos⟩
    have hnil : esOut = [] := List.eq_nil_of_length_eq_zero hlen
    rw [hnil] at he
    exact List.not_mem_nil he
  exact ⟨hnv0, by rw [hfr, hinit.2.1]; rfl, hcost, hv⟩

-- Multigraph boundary witness (`m = 5 > n = 4`, self-loop, parallel edges, cycle, isolated `3`)
-- exercising both `connectedComponentsProg_spec` and `compactVerticesProg_spec`.
example :
    let multiCycle4 : List (IndexedEdge 4) :=
      [⟨⟨0, by decide⟩, ⟨0, by decide⟩, 1, 10⟩,
       ⟨⟨0, by decide⟩, ⟨1, by decide⟩, 5, 11⟩,
       ⟨⟨0, by decide⟩, ⟨1, by decide⟩, 2, 12⟩,
       ⟨⟨1, by decide⟩, ⟨2, by decide⟩, 3, 13⟩,
       ⟨⟨2, by decide⟩, ⟨0, by decide⟩, 4, 14⟩]
    let s0 := mkInitState multiCycle4
    let g : GraphSlice := ⟨4, 5, 0⟩
    let rCC := execWordRAM s0 (connectedComponentsProg g)
    let rCV := execWordRAM s0 (compactVerticesProg g)
    rCC.1.numComps = 2 ∧ rCC.2.1.frontier = 57 ∧ rCC.2.2 ≤ 24 * 5 + 13 * 4 + 8 ∧
    (Memory.spec 16).ValidHistory s0
      ((Memory.spec 16).clientHistory s0 (connectedComponentsProg g)) ∧
    rCC.2.1.mem (rCC.1.compBase + 0) = rCC.2.1.mem (rCC.1.compBase + 1) ∧
    rCC.2.1.mem (rCC.1.compBase + 1) = rCC.2.1.mem (rCC.1.compBase + 2) ∧
    rCC.2.1.mem (rCC.1.compBase + 0) ≠ rCC.2.1.mem (rCC.1.compBase + 3) ∧
    rCV.1.numVertices = 3 ∧ rCV.1.liftBase = 20 ∧ rCV.1.edgeBase = 24 ∧
    rCV.2.1.frontier = 44 ∧ rCV.2.2 ≤ 14 * 5 + 3 * 4 + 2 ∧
    (Memory.spec 16).ValidHistory s0
      ((Memory.spec 16).clientHistory s0 (compactVerticesProg g)) := by
  intro multiCycle4 s0 g rCC rCV
  dsimp only [rCC, rCV, s0, g, execWordRAM]
  have h16 : Fits 16 16 := by decide
  have hinit := mkInitState_spec (w := 16) multiCycle4 (by decide) (by decide)
    (fun e he => by
      simp only [multiCycle4, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩)
  have hlen5 : multiCycle4.length = 5 := rfl
  have hftCC := connectedComponentsProg_spec h16 hinit.1 hinit.2.2
    (by rw [hinit.2.1, hlen5]) (by rw [hinit.2.1, hlen5]; decide)
  rw [hlen5] at hftCC
  obtain ⟨hvCC, hcostCC, _, _, _, hfrCC, _, _, _, hconnCC, hnumCC⟩ :=
    framedTriple_iff_realization.mp hftCC
  have hnum2 : (edgePartition (multiCycle4.map IndexedEdge.toWeighted)).numComponents = 2 := by
    decide
  have hftCV := compactVerticesProg_spec h16 hinit.1 hinit.2.2
    (by rw [hinit.2.1, hlen5]) (by rw [hinit.2.1, hlen5]; decide)
  rw [hlen5] at hftCV
  obtain ⟨hvCV, hcostCV, _, hliftCV, hedgeCV, _, hfrCV, _, lift, esOut, hinj, hlenOut,
      _, _, hact, hmap⟩ := framedTriple_iff_realization.mp hftCV
  have hlen0 : 0 < esOut.length := by omega
  have hlen1 : 1 < esOut.length := by omega
  have hlen3 : 3 < esOut.length := by omega
  have h0_eq : (⟨lift (esOut[0]'hlen0).u, lift (esOut[0]'hlen0).v,
      (esOut[0]'hlen0).weight, (esOut[0]'hlen0).id⟩ :
      IndexedEdge 4) = multiCycle4[0] := by
    have := congrArg (fun l => l[0]?) hmap
    simp only [List.getElem?_map, List.getElem?_eq_getElem hlen0,
      List.getElem?_eq_getElem (by decide : 0 < multiCycle4.length),
      Option.map_some, Option.some.injEq] at this
    exact this
  have h1_eq : (⟨lift (esOut[1]'hlen1).u, lift (esOut[1]'hlen1).v,
      (esOut[1]'hlen1).weight, (esOut[1]'hlen1).id⟩ :
      IndexedEdge 4) = multiCycle4[1] := by
    have := congrArg (fun l => l[1]?) hmap
    simp only [List.getElem?_map, List.getElem?_eq_getElem hlen1,
      List.getElem?_eq_getElem (by decide : 1 < multiCycle4.length),
      Option.map_some, Option.some.injEq] at this
    exact this
  have h3_eq : (⟨lift (esOut[3]'hlen3).u, lift (esOut[3]'hlen3).v,
      (esOut[3]'hlen3).weight, (esOut[3]'hlen3).id⟩ :
      IndexedEdge 4) = multiCycle4[3] := by
    have := congrArg (fun l => l[3]?) hmap
    simp only [List.getElem?_map, List.getElem?_eq_getElem hlen3,
      List.getElem?_eq_getElem (by decide : 3 < multiCycle4.length),
      Option.map_some, Option.some.injEq] at this
    exact this
  have hnv : rCV.1.numVertices = 3 := by
    dsimp only [rCV, s0, g, execWordRAM]
    let S : Finset (Fin 4) := {⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩}
    have hScard : S.card = 3 := by decide
    have himg : Finset.univ.image lift = S := by
      ext x
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨y, rfl⟩
        obtain ⟨e, he, hy⟩ := hact y
        have he' :
            (⟨lift e.u, lift e.v, e.weight, e.id⟩ : IndexedEdge 4) ∈ multiCycle4 := by
          have hmem := List.mem_map_of_mem
            (f := fun e => (⟨lift e.u, lift e.v, e.weight, e.id⟩ : IndexedEdge 4)) he
          rw [hmap] at hmem; exact hmem
        simp only [multiCycle4, List.mem_cons, List.not_mem_nil, or_false] at he'
        rcases he' with h0 | h1 | h2 | h3 | h4
        · rcases hy with rfl | rfl
          · have : lift e.u = ⟨0, by decide⟩ := congrArg IndexedEdge.u h0
            rw [this]; simp [S]
          · have : lift e.v = ⟨0, by decide⟩ := congrArg IndexedEdge.v h0
            rw [this]; simp [S]
        · rcases hy with rfl | rfl
          · have : lift e.u = ⟨0, by decide⟩ := congrArg IndexedEdge.u h1
            rw [this]; simp [S]
          · have : lift e.v = ⟨1, by decide⟩ := congrArg IndexedEdge.v h1
            rw [this]; simp [S]
        · rcases hy with rfl | rfl
          · have : lift e.u = ⟨0, by decide⟩ := congrArg IndexedEdge.u h2
            rw [this]; simp [S]
          · have : lift e.v = ⟨1, by decide⟩ := congrArg IndexedEdge.v h2
            rw [this]; simp [S]
        · rcases hy with rfl | rfl
          · have : lift e.u = ⟨1, by decide⟩ := congrArg IndexedEdge.u h3
            rw [this]; simp [S]
          · have : lift e.v = ⟨2, by decide⟩ := congrArg IndexedEdge.v h3
            rw [this]; simp [S]
        · rcases hy with rfl | rfl
          · have : lift e.u = ⟨2, by decide⟩ := congrArg IndexedEdge.u h4
            rw [this]; simp [S]
          · have : lift e.v = ⟨0, by decide⟩ := congrArg IndexedEdge.v h4
            rw [this]; simp [S]
      · intro hx
        simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact ⟨_, congrArg IndexedEdge.u h0_eq⟩
        · exact ⟨_, congrArg IndexedEdge.v h1_eq⟩
        · exact ⟨_, congrArg IndexedEdge.v h3_eq⟩
    have hcard := (Finset.card_image_of_injective Finset.univ hinj).trans (Finset.card_fin _)
    exact hcard.symm.trans ((congrArg Finset.card himg).trans hScard)
  refine ⟨hnumCC.trans hnum2, by rw [hfrCC, hinit.2.1]; rfl, hcostCC, hvCC,
    (hconnCC ⟨0, by decide⟩ ⟨1, by decide⟩).mpr (by decide),
    (hconnCC ⟨1, by decide⟩ ⟨2, by decide⟩).mpr (by decide),
    fun heq => absurd ((hconnCC ⟨0, by decide⟩ ⟨3, by decide⟩).mp heq) (by decide),
    hnv, by rw [hliftCV, hinit.2.1]; rfl, by rw [hedgeCV, hinit.2.1]; rfl,
    by rw [hfrCV, hinit.2.1]; rfl, hcostCV, hvCV⟩

/-! ## Composite `realize` pipeline over `Components` `WordEncoding` boundaries -/

private def compPipelineProg (g : GraphSlice) :
    Memory.Prog (ComponentsResult × CompactResult × ℕ) := do
  let cc ← connectedComponentsProg g
  let comp ← compactVerticesProg g
  let conBase ← contractEdgesProg ⟨g.numEdges, g.edgeBase, cc.compBase⟩
  pure (cc, comp, conBase)

private def compPipelineRawPre (w : ℕ) (g : GraphSlice) (s : Memory.State) : Prop :=
  let cc := (Memory.spec 0).clientResult s (connectedComponentsProg g)
  let s1 := (Memory.spec 0).clientState s (connectedComponentsProg g)
  let s2 := (Memory.spec 0).clientState s1 (compactVerticesProg g)
  Fits w 16 ∧
  g.edgeBase + 4 * g.numEdges ≤ s.frontier ∧
  Fits w (s.frontier + (4 * g.numVertices + 4 * g.numEdges + 1)) ∧
  (∀ j < g.numEdges,
    s.mem (g.edgeBase + 4 * j) < g.numVertices ∧
    s.mem (g.edgeBase + 4 * j + 1) < g.numVertices) ∧
  g.edgeBase + 4 * g.numEdges ≤ s1.frontier ∧
  Fits w (s1.frontier + (g.numVertices + 4 * g.numEdges + 1)) ∧
  (∀ j < g.numEdges,
    s1.mem (g.edgeBase + 4 * j) < g.numVertices ∧
    s1.mem (g.edgeBase + 4 * j + 1) < g.numVertices) ∧
  Fits w (s2.frontier + 4 * g.numEdges) ∧
  ∀ j < g.numEdges,
    g.edgeBase + 4 * j + 3 < s2.frontier ∧
    cc.compBase + s2.mem (g.edgeBase + 4 * j) < s2.frontier ∧
    cc.compBase + s2.mem (g.edgeBase + 4 * j + 1) < s2.frontier

-- Cross-program `realize` composition exercising `realizes_connectedComponentsProg`,
-- `realizes_compactVerticesProg`, and `realizes_contractEdgesProg` end-to-end with `work = 0`.
example : Realizes .exact compPipelineProg
    WordEncoding.encode WordEncoding.encode
    (fun w g s =>
      Fits w 16 ∧
      g.edgeBase + 4 * g.numEdges ≤ s.frontier ∧
      Fits w (s.frontier + (5 * g.numVertices + 12 * g.numEdges + 2)) ∧
      ∀ j < g.numEdges,
        s.mem (g.edgeBase + 4 * j) < g.numVertices ∧
        s.mem (g.edgeBase + 4 * j + 1) < g.numVertices)
    (fun _ _ => 0) := by
  have hraw : Realizes .exact compPipelineProg WordEncoding.encode WordEncoding.encode
      compPipelineRawPre (fun _ _ => 0) := by
    unfold compPipelineProg
    realize [realizes_connectedComponentsProg, realizes_compactVerticesProg,
      realizes_contractEdgesProg]
    all_goals
      rcases h with ⟨h16, h1, h2, h3, h4, h5, h6, h7, h8⟩
      first
      | exact h16 | exact h1 | exact h2 | exact h3
      | exact h4 | exact h5 | exact h6 | exact h7 | exact h8
  refine hraw.consequence (fun w g s _ hmem h => ?_) (fun _ _ => le_rfl)
  obtain ⟨h16, hin_lt, hfit, hedges⟩ := h
  dsimp only [compPipelineRawPre]
  let es : List (IndexedEdge g.numVertices) :=
    List.ofFn fun i : Fin g.numEdges =>
      ⟨⟨s.mem (g.edgeBase + 4 * i.val), (hedges i.val i.isLt).1⟩,
       ⟨s.mem (g.edgeBase + 4 * i.val + 1), (hedges i.val i.isLt).2⟩,
       s.mem (g.edgeBase + 4 * i.val + 2), s.mem (g.edgeBase + 4 * i.val + 3)⟩
  have hlen : es.length = g.numEdges := List.length_ofFn
  have hin : HoldsIndexedEdges g.edgeBase es s.mem := fun i hi => by simp [es]
  have hft1 := connectedComponentsProg_spec h16 hmem hin
    (by rw [hlen]; exact hin_lt) (by rw [hlen]; exact hfit.of_le (by omega))
  have hes_g : (⟨g.numVertices, es.length, g.edgeBase⟩ : GraphSlice) = g := by simp [hlen]
  rw [hes_g, hlen] at hft1
  obtain ⟨_, _, hmod1, hcb1, hnc1, hfr1, hwf1, hcomp_lt1, _, _, _⟩ :=
    framedTriple_iff_realization.mp hft1
  set cc := (Memory.spec 0).clientResult s (connectedComponentsProg g)
  set s1 := (Memory.spec 0).clientState s (connectedComponentsProg g)
  have hin1 : HoldsIndexedEdges g.edgeBase es s1.mem :=
    hin.congr fun a _ ha => hmod1.mem_eq_of_not_mem (by omega) (Set.notMem_empty _)
  have hft2 := compactVerticesProg_spec h16 hwf1 hin1
    (by rw [hlen, hfr1]; omega) (by rw [hlen, hfr1]; exact hfit.of_le (by omega))
  rw [hes_g, hlen] at hft2
  obtain ⟨_, _, hmod2, _, _, _, hfr2, _, _, _, _, _, _, _, _, _⟩ :=
    framedTriple_iff_realization.mp hft2
  set s2 := (Memory.spec 0).clientState s1 (compactVerticesProg g)
  have hmem_s1 : ∀ j < g.numEdges,
      s1.mem (g.edgeBase + 4 * j) < g.numVertices ∧
      s1.mem (g.edgeBase + 4 * j + 1) < g.numVertices := fun j hj => by
    have hm0 : s1.mem (g.edgeBase + 4 * j) = s.mem (g.edgeBase + 4 * j) :=
      hmod1.mem_eq_of_not_mem (by omega) (Set.notMem_empty _)
    have hm1 : s1.mem (g.edgeBase + 4 * j + 1) = s.mem (g.edgeBase + 4 * j + 1) :=
      hmod1.mem_eq_of_not_mem (by omega) (Set.notMem_empty _)
    rw [hm0, hm1]; exact hedges j hj
  refine ⟨h16, hin_lt, hfit.of_le (by omega), hedges,
    by rw [hfr1]; omega, by rw [hfr1]; exact hfit.of_le (by omega), hmem_s1,
    by rw [hfr2, hfr1]; exact hfit.of_le (by omega), fun j hj => ?_⟩
  have he_u : s2.mem (g.edgeBase + 4 * j) = s.mem (g.edgeBase + 4 * j) :=
    (hmod2.mem_eq_of_not_mem (by rw [hfr1]; omega) (Set.notMem_empty _)).trans
      (hmod1.mem_eq_of_not_mem (by omega) (Set.notMem_empty _))
  have he_v : s2.mem (g.edgeBase + 4 * j + 1) = s.mem (g.edgeBase + 4 * j + 1) :=
    (hmod2.mem_eq_of_not_mem (by rw [hfr1]; omega) (Set.notMem_empty _)).trans
      (hmod1.mem_eq_of_not_mem (by omega) (Set.notMem_empty _))
  have hu_lt := (hedges j hj).1
  have hv_lt := (hedges j hj).2
  rw [he_u, he_v, hfr2, hfr1, hcb1]
  omega

end CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.GraphOpsComponents
