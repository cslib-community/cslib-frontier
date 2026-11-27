/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.DenseCase.Driver
import CslibFrontier.Computability.WordRAM.Realization.Program.Standard
import CslibFrontier.Tactic.Fits
import CslibFrontier.Tactic.Realize
import CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.GraphOpsTestSupport
import Mathlib.Tactic.FinCases

/-!
# Worked Tests for `DenseCase.Driver` (`denseCaseProg`)

Exercises `denseCaseProg`, `realizes_denseCaseProg`, `denseCaseProg_spec`, and
`denseCaseProg_spec_of_dense` under private `module` encapsulation:
1. Empty edge list (`m = 0, n = 4`).
2. Single-edge graph (`m = 1, n = 3`) with ID preservation and deterministic width-blind
   `Program .standard` lowering via `Realizes.exists_standard_basis_init_program_state_from_words`.
3. Non-trivial multigraph (`n = 5, m = 7`) with a self-loop, parallel edges (reversed endpoints),
   duplicate weights, heavier cycle edges, and an isolated vertex via `denseCaseProg_spec_of_dense`.
4. Composite `realize [realizes_dedupSimpleEdgesProg, realizes_denseCaseProg]` pipeline over
   `GraphSlice`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.DenseCaseDriver

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.Algorithms.Lean.Kruskal Cslib.Algorithms.WordRAM.MinimumSpanningForest
open Cslib.Algorithms.WordRAM.MinimumSpanningForest.DenseCase
open Cslib.Query.MinimumSpanningForest
open CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.GraphOpsTestSupport

/-! ## 1. Boundary test: `m = 0` empty graph -/

private theorem denseCase_empty_spec :
    let es : List (IndexedEdge 4) := []
    let s := mkInitState es
    let prog := denseCaseProg ⟨4, 0, 0⟩
    let res := (Memory.spec 0).clientResult s prog
    let s' := (Memory.spec 0).clientState s prog
    res.numVertices = 4 ∧
    res.numEdges = 0 ∧
    s.frontier ≤ res.edgeBase ∧
    s'.frontier ≤ 35 ∧
    memoryCost prog s ≤ 83 ∧
    (∃ msfEs : List (IndexedEdge 4),
      msfEs = [] ∧
      HoldsIndexedEdges res.edgeBase msfEs s'.mem ∧
      IsMinSpanningForest (es.map IndexedEdge.toWeighted) (msfEs.map IndexedEdge.toWeighted)) := by
  let es : List (IndexedEdge 4) := []
  let s := mkInitState es
  obtain ⟨hwf, hfr, hin⟩ := mkInitState_spec (w := 16) es (by decide) (by decide)
    (fun _ h => by simp [es] at h)
  have hfr0 : s.frontier = 0 := hfr
  have hft := denseCaseProg_spec (w := 16) (n := 4) (edgeBase := 0) (es := es) (s := s)
    (by decide) hwf hin (by rw [hfr0]; decide) (by rw [hfr0]; decide)
  obtain ⟨_, hcost, _, hnv, hge, _, hfr_le, _, msfEs, hmsf_len, hmsf_holds, hmsf_sub, hmsf_msf⟩ :=
    framedTriple_iff_realization.mp hft
  have hmsf_nil : msfEs = [] := by
    have := hmsf_sub.length_le
    simp only [es, List.length_nil] at this
    exact List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero this)
  have hne0 : ((Memory.spec 0).clientResult s (denseCaseProg ⟨4, 0, 0⟩)).numEdges = 0 := by
    change ((Memory.spec 0).clientResult s (denseCaseProg ⟨4, es.length, 0⟩)).numEdges = 0
    rw [← hmsf_len, hmsf_nil, List.length_nil]
  refine ⟨hnv, hne0, hge, ?_, ?_, msfEs, hmsf_nil, hmsf_holds, hmsf_msf⟩
  · have hbeta : Nat.iterClogBeta (2 * 0 / 4) 4 = 2 := by decide
    dsimp only [s, es, List.length_nil] at hfr_le hfr0
    rw [hbeta, hfr0] at hfr_le
    omega
  · simp only [s, es, List.length_nil, Nat.mul_zero, Nat.add_zero, Nat.zero_mul] at hcost
    exact hcost

/-! ## 2. Single-edge `m = 1` test and `Program .standard` lowering witness -/

private def oneEdgeEs : List (IndexedEdge 3) :=
  [⟨0, 2, 7, 42⟩]

private def oneEdgeWords : List ℕ :=
  [3, 1, 4, 0, 2, 7, 42]

private theorem oneEdge_spec_facts :
    let s := Memory.State.init oneEdgeWords
    let g : GraphSlice := ⟨3, 1, 4⟩
    let prog := denseCaseProg g
    let res := (Memory.spec 0).clientResult s prog
    let s' := (Memory.spec 0).clientState s prog
    (Memory.spec 16).ValidHistory s ((Memory.spec 16).clientHistory s prog) ∧
    res.numVertices = 3 ∧
    res.numEdges = 1 ∧
    s.frontier ≤ res.edgeBase ∧
    HoldsIndexedEdges res.edgeBase oneEdgeEs s'.mem ∧
    s'.frontier ≤ 208 ∧
    memoryCost prog s ≤ 1905 := by
  let s := Memory.State.init oneEdgeWords
  have hwf : Memory.WellFormed 16 s := Memory.wellFormed_init (by decide) (by decide)
  have hin : HoldsIndexedEdges 4 oneEdgeEs s.mem := fun i hi => by
    simp only [oneEdgeEs, List.length_cons, List.length_nil] at hi
    have hi0 : i = 0 := by omega
    subst hi0
    exact ⟨rfl, rfl, rfl, rfl⟩
  have hbeta : Nat.iterClogBeta (2 * oneEdgeEs.length / 3) 3 = 2 := by decide
  have hft := denseCaseProg_spec (w := 16) (n := 3) (edgeBase := 4) (es := oneEdgeEs) (s := s)
    (by decide) hwf hin (by decide) (by rw [hbeta]; decide)
  obtain ⟨hv, hcost, _, hnv, hge, _, hfr_le, _, msfEs, hmsf_len, hmsf_holds, hmsf_sub, hmsf_msf⟩ :=
    framedTriple_iff_realization.mp hft
  have hmsf_eq : msfEs = oneEdgeEs := by
    have hnon : msfEs ≠ [] := by
      intro hem
      have hpart := hmsf_msf.1.2.2
      rw [hem, List.map_nil] at hpart
      have hc0 : (edgePartition (oneEdgeEs.map IndexedEdge.toWeighted)).numComponents = 2 := by
        decide
      have hc1 : (edgePartition ([] : List (WeightedEdge 3 ℕ))).numComponents = 3 := by
        decide
      rw [← hpart] at hc0
      omega
    rcases msfEs with _ | ⟨e, rest⟩
    · exact absurd rfl hnon
    · have hlen_le := hmsf_sub.length_le
      simp only [oneEdgeEs, List.length_cons, List.length_nil] at hlen_le
      have hrest : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hrest
      have he_mem : e ∈ oneEdgeEs := hmsf_sub.subset List.mem_cons_self
      simp only [oneEdgeEs, List.mem_singleton] at he_mem
      subst he_mem
      rfl
  have hne1 : ((Memory.spec 0).clientResult s (denseCaseProg ⟨3, 1, 4⟩)).numEdges = 1 := by
    change ((Memory.spec 0).clientResult s (denseCaseProg ⟨3, oneEdgeEs.length, 4⟩)).numEdges = 1
    rw [← hmsf_len, hmsf_eq]
    rfl
  refine ⟨hv, hnv, hne1, hge, hmsf_eq ▸ hmsf_holds, ?_, ?_⟩
  · rw [hbeta] at hfr_le; exact hfr_le.trans (by decide)
  · rw [hbeta] at hcost; exact hcost.trans (by decide)

private theorem exists_standard_denseCaseProg_oneEdge_halts :
    ∃ r C pc : ℕ, ∃ prog : Program .standard r, ¬prog.ReadsWidth ∧ prog.IsRandFree ∧
      ∃ _frontier : Fin r, ∃ out : Fin 3 → Fin r, ∃ y n,
        Runs 16 prog (State.init oneEdgeWords) ⟨pc, y⟩ n ∧
        step 16 prog ⟨pc, y⟩ = .halt 3 ∧
        y.regs (out 1) = 1 ∧
        n + 1 ≤ C * (memoryCost (denseCaseProg ⟨3, 1, 4⟩)
          (Memory.State.init oneEdgeWords) + 1) + 1 := by
  obtain ⟨r, C, pc, prog, hnw, _frontier, out, hrun⟩ :=
    realizes_denseCaseProg.exists_standard_basis_init_program_state_from_words (0 : Fin 3)
  have hprog_rf : (stripRand prog).IsRandFree := isRandFree_stripRand prog
  have hprog_nw : ¬(stripRand prog).ReadsWidth := not_readsWidth_stripRand hnw
  let g : GraphSlice := ⟨3, 1, 4⟩
  have hlayout :
      ∀ j : Fin 3, oneEdgeWords.getD j.val 0 = WordEncoding.encode g j := by
    intro j
    fin_cases j <;> rfl
  have hsafe :
      Fits 16 16 ∧ g.edgeBase + 4 * g.numEdges ≤ (Memory.State.init oneEdgeWords).frontier ∧
      Fits 16 ((Memory.State.init oneEdgeWords).frontier + (21 * g.numEdges + 8 * g.numVertices +
        76 * g.numEdges * Nat.iterClogBeta ((2 * g.numEdges) / g.numVertices) g.numVertices +
          3)) ∧
      ∀ j < g.numEdges,
        (Memory.State.init oneEdgeWords).mem (g.edgeBase + 4 * j) < g.numVertices ∧
        (Memory.State.init oneEdgeWords).mem (g.edgeBase + 4 * j + 1) < g.numVertices := by
    have hbeta : Nat.iterClogBeta (2 * 1 / 3) 3 = 2 := by decide
    refine ⟨by decide, by decide, by dsimp only [g]; rw [hbeta]; decide, fun j hj => ?_⟩
    dsimp only [g] at hj
    have hj0 : j = 0 := by omega
    subst hj0
    decide
  obtain ⟨hv, hnv, hne, _, _, _, _⟩ := oneEdge_spec_facts
  obtain ⟨y, n, hruns, hhalt, _, hregs, hsteps⟩ :=
    hrun 16 g oneEdgeWords hlayout (by decide) (by decide) (by decide) hsafe hv
  have hres_w := clientResult_width (p := denseCaseProg g) (s := Memory.State.init oneEdgeWords) 16
  have h0 : WordEncoding.encode ((Memory.spec 0).clientResult
      (Memory.State.init oneEdgeWords) (denseCaseProg g)) (0 : Fin 3) = 3 := hnv
  have hhalt' : step 16 prog ⟨pc, y⟩ = .halt 3 := by
    rw [hhalt, hres_w, h0]
  have hreg1 : y.regs (out 1) = 1 := by
    rw [hregs 1, hres_w]
    exact hne
  exact ⟨r, C, pc, stripRand prog, hprog_nw, hprog_rf, _frontier, out, y, n,
    runs_stripRand hruns, step_stripRand_of_halt hhalt', hreg1, by simpa using hsteps⟩

/-! ## 3. Non-trivial multigraph test via `denseCaseProg_spec_of_dense` -/

private def multiEs : List (IndexedEdge 5) :=
  [ ⟨1, 1, 1, 100⟩,
    ⟨0, 1, 9, 101⟩,
    ⟨1, 0, 3, 102⟩,
    ⟨1, 2, 3, 103⟩,
    ⟨2, 3, 3, 104⟩,
    ⟨0, 2, 8, 105⟩,
    ⟨3, 0, 6, 106⟩ ]

private def multiRefForest : List (WeightedEdge 5 ℕ) :=
  [ ⟨1, 0, 3⟩, ⟨1, 2, 3⟩, ⟨2, 3, 3⟩ ]

private theorem multiRefForest_isMSF :
    IsMinSpanningForest (multiEs.map IndexedEdge.toWeighted) multiRefForest := by
  have hsub : multiRefForest.Subperm (multiEs.map IndexedEdge.toWeighted) := by
    have hs : List.Sublist multiRefForest
        [⟨1, 1, 1⟩, ⟨0, 1, 9⟩, ⟨1, 0, 3⟩, ⟨1, 2, 3⟩, ⟨2, 3, 3⟩, ⟨0, 2, 8⟩, ⟨3, 0, 6⟩] := by
      exact .cons _ (.cons _ (.cons_cons _ (.cons_cons _ (.cons_cons _
        (.cons _ (.cons _ .slnil))))))
    exact hs.subperm
  have hac : IsAcyclic multiRefForest := by
    rw [isAcyclic_iff]
    decide
  have hpart : edgePartition multiRefForest =
      edgePartition (multiEs.map IndexedEdge.toWeighted) := by
    apply DisjointSet.Partition.ext
    intro x y
    fin_cases x <;> fin_cases y <;> decide
  refine ⟨⟨hsub, hac, hpart⟩, fun G' hG' => ?_⟩
  have hc_eq : (edgePartition G').numComponents = 2 := by
    rw [hG'.2.2]
    decide
  have hlen : G'.length = 3 := by
    have ha := (isAcyclic_iff G').mp hG'.2.1
    omega
  have hwt3 : ∀ e ∈ G', 3 ≤ e.weight := by
    intro e he
    have he_mem := hG'.1.subset he
    simp only [multiEs, List.mem_map, List.mem_cons, List.not_mem_nil, or_false,
      IndexedEdge.toWeighted] at he_mem
    rcases he_mem with ⟨x, rfl | rfl | rfl | rfl | rfl | rfl | rfl, rfl⟩
    · exfalso
      have ha := isAcyclic_sublist (List.singleton_sublist.mpr he) hG'.2.1
      rw [isAcyclic_iff] at ha
      simp only [edgePartition, edgePartitionFrom_cons, edgePartitionFrom_nil,
        List.length_singleton] at ha
      have : (DisjointSet.Partition.discrete 5).rel (1 : Fin 5) 1 = true :=
        (DisjointSet.Partition.discrete 5).refl 1
      rw [DisjointSet.Partition.merge_of_rel this] at ha
      simp [DisjointSet.Partition.numComponents_discrete] at ha
    all_goals decide
  have hsum : ∀ l : List (WeightedEdge 5 ℕ), (∀ e ∈ l, 3 ≤ e.weight) →
      3 * l.length ≤ totalWeight l := by
    intro l hl
    induction l with
    | nil => simp [totalWeight]
    | cons a t ih =>
      have h1 := hl a List.mem_cons_self
      have h2 := ih fun e he => hl e (List.mem_cons_of_mem _ he)
      simp only [totalWeight, List.map_cons, List.sum_cons, List.length_cons] at h2 ⊢
      omega
  have htot_ref : totalWeight multiRefForest = 9 := by decide
  rw [htot_ref]
  calc 9 = 3 * G'.length := by omega
    _ ≤ totalWeight G' := hsum G' hwt3

private theorem denseCase_multi_spec :
    let s := mkInitState multiEs
    let prog := denseCaseProg ⟨5, 7, 0⟩
    let res := (Memory.spec 0).clientResult s prog
    let s' := (Memory.spec 0).clientState s prog
    res.numVertices = 5 ∧
    res.numEdges = 3 ∧
    s.frontier ≤ res.edgeBase ∧
    s'.frontier ≤ 23626 ∧
    memoryCost prog s ≤ 274347 ∧
    ∃ msfEs : List (IndexedEdge 5),
      msfEs.length = 3 ∧
      HoldsIndexedEdges res.edgeBase msfEs s'.mem ∧
      msfEs.Subperm multiEs ∧
      totalWeight (msfEs.map IndexedEdge.toWeighted) = 9 ∧
      (∀ e ∈ msfEs, e.id = 102 ∨ e.id = 103 ∨ e.id = 104) ∧
      IsMinSpanningForest (multiEs.map IndexedEdge.toWeighted)
        (msfEs.map IndexedEdge.toWeighted) := by
  let s := mkInitState multiEs
  obtain ⟨hwf, hfr, hin⟩ := mkInitState_spec (w := 20) multiEs (by decide) (by decide)
    (fun e he => by
      simp only [multiEs, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩)
  have hfr0 : s.frontier = 28 := hfr
  have hdense : 5 * max 1 (Nat.iterLog 3 5) ≤ 2 * multiEs.length := by decide
  have hft := denseCaseProg_spec_of_dense (w := 20) (n := 5) (n₀ := 5) (edgeBase := 0)
    (es := multiEs) (s := s) (by decide) hwf le_rfl hdense hin (by rw [hfr0]; decide)
    (by rw [hfr0]; decide)
  obtain ⟨_, hcost, _, hnv, hge, _, hfr_le, _, msfEs, hmsf_len, hmsf_holds, hmsf_sub, hmsf_msf⟩ :=
    framedTriple_iff_realization.mp hft
  have hmlen : multiEs.length = 7 := rfl
  rw [hmlen] at hnv hge hcost hfr_le hmsf_holds hmsf_len
  have hpart := hmsf_msf.1.2.2
  have hc_ref : (edgePartition (multiEs.map IndexedEdge.toWeighted)).numComponents = 2 := by
    decide
  have hlen3 : msfEs.length = 3 := by
    have ha := (isAcyclic_iff (msfEs.map IndexedEdge.toWeighted)).mp hmsf_msf.1.2.1
    rw [hpart, hc_ref, List.length_map] at ha
    omega
  have hne3 : ((Memory.spec 0).clientResult s (denseCaseProg ⟨5, 7, 0⟩)).numEdges = 3 := by
    rw [← hmsf_len, hlen3]
  have htot9 : totalWeight (msfEs.map IndexedEdge.toWeighted) = 9 := by
    have h1 := hmsf_msf.2 multiRefForest multiRefForest_isMSF.1
    have h2 := multiRefForest_isMSF.2 (msfEs.map IndexedEdge.toWeighted) hmsf_msf.1
    have htot_ref : totalWeight multiRefForest = 9 := by decide
    omega
  have hids : ∀ e ∈ msfEs, e.id = 102 ∨ e.id = 103 ∨ e.id = 104 := by
    have hge3 : ∀ e ∈ msfEs, 3 ≤ e.weight := by
      intro e he
      have hem := hmsf_sub.subset he
      simp only [multiEs, List.mem_cons, List.not_mem_nil, or_false] at hem
      rcases hem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exfalso
        have ha := isAcyclic_sublist (List.singleton_sublist.mpr (List.mem_map.mpr ⟨_, he, rfl⟩))
          hmsf_msf.1.2.1
        rw [isAcyclic_iff] at ha
        simp only [edgePartition, edgePartitionFrom_cons, edgePartitionFrom_nil,
          List.length_singleton, IndexedEdge.toWeighted] at ha
        have : (DisjointSet.Partition.discrete 5).rel (1 : Fin 5) 1 = true :=
          (DisjointSet.Partition.discrete 5).refl 1
        rw [DisjointSet.Partition.merge_of_rel this] at ha
        simp [DisjointSet.Partition.numComponents_discrete] at ha
      all_goals decide
    have hsum_drop : ∀ (x : IndexedEdge 5) (l : List (IndexedEdge 5)),
        List.Subperm (x :: l) multiEs → (∀ y ∈ x :: l, 3 ≤ y.weight) →
        x.weight + 3 * l.length ≤ totalWeight ((x :: l).map IndexedEdge.toWeighted) := by
      intro x l _ hge'
      have hsum_l : ∀ (ys : List (IndexedEdge 5)), (∀ y ∈ ys, 3 ≤ y.weight) →
          3 * ys.length ≤ totalWeight (ys.map IndexedEdge.toWeighted) := by
        intro ys hys
        induction ys with
        | nil => simp [totalWeight]
        | cons a t ih =>
          have h1 := hys a List.mem_cons_self
          have h2 := ih fun y hy => hys y (List.mem_cons_of_mem _ hy)
          simp only [totalWeight, List.map_cons, List.sum_cons, List.length_cons,
            IndexedEdge.toWeighted] at h2 ⊢
          omega
      have hl := hsum_l l fun y hy => hge' y (List.mem_cons_of_mem _ hy)
      simp only [totalWeight, List.map_cons, List.sum_cons, IndexedEdge.toWeighted] at hl ⊢
      omega
    intro e he
    let l := msfEs.erase e
    have hperm : (e :: l).Perm msfEs := (List.perm_cons_erase he).symm
    have hsub' : (e :: l).Subperm multiEs := hperm.subperm.trans hmsf_sub
    have hlen_l : l.length = 2 := by
      have := hperm.length_eq
      simp only [List.length_cons] at this
      omega
    have htot' : totalWeight ((e :: l).map IndexedEdge.toWeighted) = 9 := by
      rw [Perm.totalWeight_eq (hperm.map IndexedEdge.toWeighted)]
      exact htot9
    have hge_el : ∀ y ∈ e :: l, 3 ≤ y.weight := fun y hy => hge3 y (hperm.subset hy)
    have hbd := hsum_drop e l hsub' hge_el
    have hew : e.weight ≤ 3 := by omega
    have hem := hmsf_sub.subset he
    simp only [multiEs, List.mem_cons, List.not_mem_nil, or_false] at hem
    rcases hem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exfalso; exact absurd (hge3 _ he) (by decide)
    · exfalso; dsimp only at hew; omega
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
    · exfalso; dsimp only at hew; omega
    · exfalso; dsimp only at hew; omega
  refine ⟨hnv, hne3, hge, hfr_le.trans (by rw [hfr0]), hcost.trans (by decide),
    msfEs, hlen3, hmsf_holds, hmsf_sub, htot9, hids, hmsf_msf⟩

/-! ## 4. Composite `realize` pipeline over `GraphSlice` -/

private def dedupThenDenseProg (g : GraphSlice) : Memory.Prog GraphSlice := do
  let ded ← dedupSimpleEdgesProg g
  denseCaseProg ded

private theorem realizes_dedupThenDenseProg : Realizes .exact
    dedupThenDenseProg WordEncoding.encode WordEncoding.encode
    (fun w g s =>
      let ded := (Memory.spec 0).clientResult s (dedupSimpleEdgesProg g)
      let s₁ := (Memory.spec 0).clientState s (dedupSimpleEdgesProg g)
      Fits w 16 ∧ g.edgeBase + 4 * g.numEdges ≤ s.frontier ∧
      Fits w (s.frontier + (13 * g.numEdges + 2 * g.numVertices)) ∧
      (∀ j < g.numEdges,
        s.mem (g.edgeBase + 4 * j) < g.numVertices ∧
        s.mem (g.edgeBase + 4 * j + 1) < g.numVertices) ∧
      ded.edgeBase + 4 * ded.numEdges ≤ s₁.frontier ∧
      Fits w (s₁.frontier + (21 * ded.numEdges + 8 * ded.numVertices +
        76 * ded.numEdges * Nat.iterClogBeta ((2 * ded.numEdges) / ded.numVertices)
          ded.numVertices + 3)) ∧
      ∀ j < ded.numEdges,
        s₁.mem (ded.edgeBase + 4 * j) < ded.numVertices ∧
        s₁.mem (ded.edgeBase + 4 * j + 1) < ded.numVertices)
    (fun _ _ => 0) := by
  unfold dedupThenDenseProg
  realize [realizes_dedupSimpleEdgesProg, realizes_denseCaseProg]
  all_goals
    rcases h with ⟨h16, h1, h2, h3, h4, h5, h6⟩
    first | exact h16 | exact h1 | exact h2 | exact h3 | exact h4 | exact h5 | exact h6

end CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.DenseCaseDriver
