/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.Partition.Outer
import CslibFrontier.Computability.WordRAM.Realization.Program.Standard
import CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.GraphOpsTestSupport
import CslibFrontier.Tactic.Fits

/-!
# Tests for Word-RAM Minimum Spanning Forest Outer Partition Layer

Exercises `partitionProg_spec`, `partRunRound_spec`, `partRoundInit_spec`/`partDjpLoop_spec`/
`partRoundFinish_spec`, `realizes_partitionProg`, and `Bridges` graph-theory consequences under
`module` encapsulation across:

1. Empty vertex graph (`n = 0`).
2. Isolated vertices (`n = 3, m = 0`) with `Bridges` optDepth and MSF lifting.
3. Connected `K_3` (`n = 3, m = 3, maxsize = 4`).
4. Overlapping conglomerates on `K_3` (`maxsize = 2`, two chained rounds merging overlapping
   components via `vOut`) with `Bridges.partition_optDepth_sum_le`,
   `partition_conglom_active_verts_le`, and `partition_isMinSpanningForest`.
5. Multigraph boundaries: parallel-edge loopless graph (`m = 3, maxsize = 3`) via `partRunRound`
   internals and simple `m > n` graph (`K_4 \ e`, `n = 4, m = 5`).
6. Deterministic width-blind `Program .standard` lowering via
   `realizes_partitionProg.exists_standard_basis_init_program_state_from_words` and `stripRand`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.PartitionOuter

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.DisjointSet
open Cslib.Algorithms.Lean.Kruskal
open Cslib.Query.MinimumSpanningForest
open Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap
open Cslib.Algorithms.WordRAM.MinimumSpanningForest
open CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.GraphOpsTestSupport

private theorem isSimple_of_pairs {n : ℕ} {es : List (IndexedEdge n)}
    (hdiag : ∀ i : Fin es.length, (es[i.val]'i.isLt).u ≠ (es[i.val]'i.isLt).v)
    (hinj : ∀ i j : Fin es.length, i.val < j.val →
      let ei := es[i.val]'i.isLt
      let ej := es[j.val]'j.isLt
      ¬((ei.u = ej.u ∧ ei.v = ej.v) ∨ (ei.u = ej.v ∧ ei.v = ej.u))) :
    IsSimple (edgeEnds (es.map IndexedEdge.toWeighted)) := by
  refine (isSimple_iff _).mpr ⟨fun i => ?_, fun i j hij => ?_⟩
  · simpa [edgeEnds, IndexedEdge.toWeighted, Sym2.mk_isDiag_iff] using
      hdiag ⟨i.val, by simpa using i.isLt⟩
  · by_contra hne
    have h_sym : s((es[i.val]'(by simpa using i.isLt)).u,
        (es[i.val]'(by simpa using i.isLt)).v) =
        s((es[j.val]'(by simpa using j.isLt)).u,
        (es[j.val]'(by simpa using j.isLt)).v) := by
      simpa [edgeEnds, IndexedEdge.toWeighted] using hij
    rcases Nat.lt_trichotomy i.val j.val with hlt | heq | hgt
    · exact hinj ⟨i.val, by simpa using i.isLt⟩ ⟨j.val, by simpa using j.isLt⟩ hlt
        (Sym2.eq_iff.mp h_sym)
    · exact hne (Fin.ext heq)
    · exact hinj ⟨j.val, by simpa using j.isLt⟩ ⟨i.val, by simpa using i.isLt⟩ hgt
        (Sym2.eq_iff.mp h_sym.symm)

private theorem isMinSpanningForest_nil {n : ℕ} :
    IsMinSpanningForest ([] : List (WeightedEdge n ℕ)) [] := by
  simpa [kruskalEdges, sortEdges, kruskalScan] using
    kruskalEdges_isMinSpanningForest ([] : List (WeightedEdge n ℕ))

private theorem edgePartitionFrom_fin1_eq {xs : List (WeightedEdge 1 ℕ)}
    (p : Partition 1) : edgePartitionFrom p xs = p := by
  induction xs generalizing p with
  | nil => rfl
  | cons e rest ih =>
    have huv : e.u = e.v := Subsingleton.elim _ _
    rw [edgePartitionFrom_cons, huv, Partition.merge_of_rel (p.refl _)]
    exact ih p

private theorem edgePartition_fin1_eq_discrete {xs : List (WeightedEdge 1 ℕ)} :
    edgePartition xs = Partition.discrete 1 :=
  edgePartitionFrom_fin1_eq (Partition.discrete 1)

private theorem isMinSpanningForest_fin1_loops {xs : List (WeightedEdge 1 ℕ)} :
    IsMinSpanningForest xs [] := by
  refine ⟨⟨List.nil_subperm, by simp [IsAcyclic, IsAcyclicFrom], ?_⟩, fun F' _ => ?_⟩
  · simp [edgePartition_fin1_eq_discrete]
  · simp [totalWeight]

private theorem card_simple_fin2_le_one {k : ℕ} (hk : k = 2)
    {xs : List (IndexedEdge k)} (hs : IsSimple (edgeEnds (xs.map IndexedEdge.toWeighted))) :
    xs.length ≤ 1 := by
  subst hk
  have hsi := (isSimple_iff _).mp hs
  have hle := Fintype.card_le_of_injective
    (fun i : Fin xs.length =>
      (⟨edgeEnds (xs.map IndexedEdge.toWeighted) ⟨i.val, by simp⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsi.1 _⟩⟩ :
        {s : Sym2 (Fin 2) // s ∈ Finset.univ.filter fun s : Sym2 (Fin 2) => ¬s.IsDiag}))
    fun a b hab => Fin.ext (by
      simpa using congrArg Fin.val (hsi.2 (congrArg Subtype.val hab)))
  simp only [Fintype.card_fin, Fintype.card_coe] at hle
  exact hle.trans (by decide)

private theorem subperm_compGlobal_of_perm {n : ℕ} {rounds : List (PartitionRoundWitness n)}
    {H_rem es : List (IndexedEdge n)}
    (hperm : ((rounds.flatMap PartitionRoundWitness.compGlobal) ++ H_rem ++
      (rounds.flatMap PartitionRoundWitness.corrEdges)).Perm es) :
    (rounds.flatMap PartitionRoundWitness.compGlobal).Subperm es :=
  ((List.sublist_append_left _ _).trans (List.sublist_append_left _ _)).subperm.trans hperm.subperm

private theorem edgePartition_root_rel_mem {n : ℕ} {D : DynamicDJPTree n}
    {E : List (WeightedEdge n ℕ)} (hsub : D.treeEdges.Subperm E)
    {z : Fin n} (hz : z ∈ D.treeVerts D.numSteps) :
    (edgePartition E).rel D.root z = true := by
  have hc := D.joins_treeVerts hz
  clear hz
  induction hc with
  | refl => exact (edgePartition E).refl _
  | @tail b c _ hs ih =>
    obtain ⟨s, _, he⟩ := hs
    have he_mem : D.edge s ∈ D.treeEdges := List.mem_map.mpr ⟨s, List.mem_finRange s, rfl⟩
    have hrel := rel_edgePartitionFrom_of_mem (Partition.discrete n) he_mem
    have hrel' := edgePartition_mono_subperm hsub hrel
    dsimp only [DynamicDJPTree.ends] at he
    rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (edgePartition E).trans ih hrel'
    · exact (edgePartition E).trans ih ((edgePartition E).symm hrel')

/-! ## 1. Boundary: `n = 0` Empty Vertex Graph -/

-- Test (a): `partitionProg` on empty vertex graph `n = 0, m = 0, maxsize = 1`.
example :
    let s0 : Memory.State := ⟨fun _ => 0, 0⟩
    let d : PartSetupArgs := ⟨0, 0, 0, 1⟩
    let r := execWordRAM s0 (partitionProg d)
    partitionProgSafe 16 d s0 ∧
    (Memory.spec 16).ValidHistory s0 ((Memory.spec 16).clientHistory s0 (partitionProg d)) ∧
    r.1 = ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩ ∧ r.2.1 = s0 ∧ r.2.2 = 0 := by
  intro s0 d r
  let es : List (IndexedEdge 0) := []
  have h16 : Fits 16 16 := by decide
  have hwf : Memory.WellFormed 16 s0 := ⟨by decide, fun _ => by dsimp only [s0]; decide⟩
  have hin : HoldsIndexedEdges 0 es s0.mem := fun i hi => absurd hi (Nat.not_lt_zero _)
  have hsimp : IsSimple (edgeEnds (es.map IndexedEdge.toWeighted)) :=
    isSimple_of_pairs (fun i => Fin.elim0 (Fin.cast (by simp [es]) i))
      (fun i => Fin.elim0 (Fin.cast (by simp [es]) i))
  have hspec := partitionProg_spec h16 hwf (by decide : 1 ≤ 1) hin (by decide) (by decide) hsimp
  have hprog : partitionProg d = pure ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩ := by
    rw [partitionProg_def]; simp [d]
  refine ⟨hspec.1, hspec.2.1, ?_, ?_, ?_⟩
  · dsimp only [r, execWordRAM]; rw [hprog, StateTransitionSpec.clientResult_pure]
  · dsimp only [r, execWordRAM]; rw [hprog, StateTransitionSpec.clientState_pure]
  · dsimp only [r, execWordRAM]; rw [hprog, memoryCost_pure]

/-! ## 2. Boundary: `n = 3, m = 0` Isolated Vertices + `Bridges` -/

-- Test (b): `partitionProg` on `n = 3, m = 0, maxsize = 2` with `optDepth` and MSF bridge.
example :
    let es : List (IndexedEdge 3) := []
    let s0 := mkInitState es
    let d : PartSetupArgs := ⟨3, 0, 0, 2⟩
    let r := execWordRAM s0 (partitionProg d)
    partitionProgSafe 16 d s0 ∧
    (Memory.spec 16).ValidHistory s0 ((Memory.spec 16).clientHistory s0 (partitionProg d)) ∧
    Memory.WellFormed 16 r.2.1 ∧ r.2.1.frontier ≤ 288 ∧ r.2.2 ≤ 18000 ∧
    r.1.numComps ≤ 3 ∧ r.1.mcLen = 0 ∧ r.1.hRemLen = 0 ∧ r.1.nConglom = 3 ∧
    (∃ (rounds : List (PartitionRoundWitness 3)) (H_rem : List (IndexedEdge 3))
        (conglomFn : Fin 3 → Fin r.1.nConglom),
      H_rem = [] ∧ Function.Injective conglomFn ∧
      (rounds.map fun q => optDepth (edgeEnds (q.compLocal.map IndexedEdge.toWeighted))).sum ≤
        optDepthMN 0 3 ∧
      IsMinSpanningForest (es.map IndexedEdge.toWeighted) ([] : List (WeightedEdge 3 ℕ))) := by
  intro es s0 d r
  have hinit := mkInitState_spec (w := 16) es (by decide) (by dsimp only [es]; decide)
    (fun _ h => by simp [es] at h)
  have hsimp : IsSimple (edgeEnds (es.map IndexedEdge.toWeighted)) :=
    isSimple_of_pairs (fun i => Fin.elim0 (Fin.cast (by simp [es]) i))
      (fun i => Fin.elim0 (Fin.cast (by simp [es]) i))
  have hspec := partitionProg_spec (by decide) hinit.1 (maxsize := 2) (by decide) hinit.2.2
    (by rw [hinit.2.1]; dsimp only [es]; decide) (by rw [hinit.2.1]; dsimp only [es]; decide) hsimp
  rcases hspec with ⟨hsafe, hvh, hwf', _, _, hfr_ub, hcost, hnc_le, hmc_le, hrem_le, hcg_le,
    _, _, _, _, _, _, rounds, H_rem, conglomFn, hrl, hhl, _, hperm, hmc_len,
    _, _, _, _, hrel, hcov, hmeta, hround_ext, _, huncorr_rem, hstop_prev, huncorr_tree⟩
  have hmc0 : r.1.mcLen = 0 :=
    Nat.eq_zero_of_le_zero (by simpa [r, execWordRAM, s0, d, es] using hmc_le)
  have hrem0 : r.1.hRemLen = 0 :=
    Nat.eq_zero_of_le_zero (by simpa [r, execWordRAM, s0, d, es] using hrem_le)
  have hH_nil : H_rem = [] := List.eq_nil_of_length_eq_zero (hhl.trans hrem0)
  have hperm_len := hperm.length_eq
  rw [List.length_append, List.length_append, hH_nil, List.length_nil] at hperm_len
  have hlen_zero :
      (rounds.flatMap PartitionRoundWitness.compGlobal).length + 0 +
      (rounds.flatMap PartitionRoundWitness.corrEdges).length = 0 := by
    simpa [es] using hperm_len
  have hcg_nil : rounds.flatMap PartitionRoundWitness.compGlobal = [] :=
    List.eq_nil_of_length_eq_zero (Nat.add_eq_zero_iff.mp (Nat.add_eq_zero_iff.mp hlen_zero).1).1
  have hcorr_nil : rounds.flatMap PartitionRoundWitness.corrEdges = [] :=
    List.eq_nil_of_length_eq_zero (Nat.add_eq_zero_iff.mp hlen_zero).2
  have hq_nil : ∀ q ∈ rounds, q.compGlobal = [] := fun q hq =>
    List.flatMap_eq_nil_iff.mp hcg_nil q hq
  have hqt_nil : ∀ q ∈ rounds, q.tree.treeEdges = [] := fun q hq => by
    have hsub := List.getElem_of_mem hq
    rcases hsub with ⟨i, hi, rfl⟩
    rcases hround_ext ⟨i, hi⟩ with ⟨_, _, _, _, _, hts⟩
    have h1 := hts.length_le
    rw [hq_nil _ hq] at h1
    exact List.eq_nil_of_length_eq_zero (by simpa using h1)
  have htr_flat : (rounds.flatMap fun q => q.tree.treeEdges) = [] :=
    List.flatMap_eq_nil_iff.mpr hqt_nil
  have hinj_cg : Function.Injective conglomFn := fun x y hxy => by
    have hr := (hrel x y).mp hxy
    rw [htr_flat] at hr
    exact Partition.rel_discrete_eq_true.mp hr
  have h3_le : 3 ≤ r.1.nConglom := by
    simpa [r, execWordRAM, s0, d, es, Fintype.card_fin] using
      Fintype.card_le_of_injective conglomFn hinj_cg
  have hcg_eq : r.1.nConglom = 3 :=
    le_antisymm (by simpa [r, execWordRAM, s0, d, es] using hcg_le) h3_le
  have hopt := partition_optDepth_sum_le hsimp (subperm_compGlobal_of_perm hperm) fun i =>
    ⟨hmeta.lift_injective i, hmeta.compGlobal_verts i, hmeta.inter_prev_card_le_one i⟩
  have hmsf := partition_isMinSpanningForest (F_comps := List.replicate rounds.length [])
    (H_lift := []) (F := []) (hperm.map IndexedEdge.toWeighted)
    hcov hrel (fun i => by
      rcases hround_ext i with ⟨_, _, _, _, _, hts_i⟩
      exact ⟨hts_i, hstop_prev i⟩)
    huncorr_rem huncorr_tree (by simp)
    (fun i => by
      rw [hq_nil _ (List.getElem_mem _), List.getElem_replicate]
      simpa using isMinSpanningForest_nil)
    List.nil_subperm (by simpa [hH_nil, contractEdgeList] using isMinSpanningForest_nil)
    (by
      have hf : (List.replicate rounds.length ([] : List (WeightedEdge 3 ℕ))).flatten = [] := by
        simp
      simpa [hf, hcorr_nil] using isMinSpanningForest_nil)
  exact ⟨by simpa [s0, d, es] using hsafe, by simpa [s0, d, es] using hvh,
    by simpa [r, execWordRAM, s0, d, es] using hwf',
    by simpa [r, execWordRAM, s0, d, es, hinit.2.1] using hfr_ub,
    by simpa [r, execWordRAM, s0, d, es] using hcost,
    by simpa [r, execWordRAM, s0, d, es] using hnc_le, hmc0, hrem0, hcg_eq,
    rounds, H_rem, conglomFn, hH_nil, hinj_cg, hopt, hmsf⟩

/-! ## 3. Connected `K_3` (`maxsize = 4`, Single Round Emits Whole Graph) -/

private def esK3 : List (IndexedEdge 3) :=
  [⟨⟨0, by decide⟩, ⟨1, by decide⟩, 2, 0⟩,
   ⟨⟨1, by decide⟩, ⟨2, by decide⟩, 3, 1⟩,
   ⟨⟨0, by decide⟩, ⟨2, by decide⟩, 5, 2⟩]

private theorem isSimple_esK3 : IsSimple (edgeEnds (esK3.map IndexedEdge.toWeighted)) := by
  refine isSimple_of_pairs (fun i => by fin_cases i <;> decide) fun i j hij => ?_
  fin_cases i <;> fin_cases j <;> simp_all [esK3]

private theorem esK3_edge_between {a b : Fin 3} (hne : a ≠ b) :
    ∃ eIdx : Fin 3,
      ((esK3[eIdx.val]'eIdx.isLt).u = a ∧ (esK3[eIdx.val]'eIdx.isLt).v = b) ∨
      ((esK3[eIdx.val]'eIdx.isLt).u = b ∧ (esK3[eIdx.val]'eIdx.isLt).v = a) := by
  fin_cases a <;> fin_cases b
  all_goals first
    | exact absurd rfl hne
    | exact ⟨⟨0, by decide⟩, by decide⟩
    | exact ⟨⟨1, by decide⟩, by decide⟩
    | exact ⟨⟨2, by decide⟩, by decide⟩

-- Test (c): Single round of `partRunRound_spec` on `K_3` with `maxsize = 4`, plus `partitionProg`.
example :
    let s0 := mkInitState esK3
    let setup := (Memory.spec 0).clientResult s0 (partSetup ⟨3, 3, 0, 4⟩)
    let s1 := (Memory.spec 0).clientState s0 (partSetup ⟨3, 3, 0, 4⟩)
    let st0 : PartOuterState := ⟨0, 0, 0, 0, 0, 0, setup.sh⟩
    let prog := partRunRound (setup.env, st0)
    let rProg := execWordRAM s0 (partitionProg ⟨3, 3, 0, 4⟩)
    (Memory.spec 16).ValidHistory s1 ((Memory.spec 16).clientHistory s1 prog) ∧
    (∃ (r : PartitionRoundWitness 3) (corr : List (Fin 3)),
      r.numVerts = 3 ∧ r.verts = Finset.univ ∧ corr = [] ∧
      r.compGlobal.Perm esK3 ∧ r.tree.numSteps = 2) ∧
    partitionProgSafe 16 ⟨3, 3, 0, 4⟩ s0 ∧
    (Memory.spec 16).ValidHistory s0
      ((Memory.spec 16).clientHistory s0 (partitionProg ⟨3, 3, 0, 4⟩)) ∧
    rProg.1.mcLen = 0 ∧ 1 ≤ rProg.1.numComps ∧ rProg.1.numComps ≤ 3 ∧
    (∃ (rounds : List (PartitionRoundWitness 3)),
      (rounds.map fun q => optDepth (edgeEnds (q.compLocal.map IndexedEdge.toWeighted))).sum ≤
        optDepthMN 3 3) := by
  intro s0 setup s1 st0 prog rProg
  have hinit := mkInitState_spec (w := 16) esK3 (by decide) (by decide)
    (fun e he => by simp only [esK3, List.mem_cons, List.not_mem_nil, or_false] at he
                    rcases he with rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩)
  have hsetup := partSetup_spec (w := 16) (n := 3) (edgeBase := 0) (maxsize := 4) (by decide)
    hinit.1 (by decide) (by decide) hinit.2.2 (by rw [hinit.2.1]; decide)
    (by rw [hinit.2.1]; decide)
  rcases hsetup with ⟨_, _, _, _, hm, _, hmax, _, hsh_eq, hs1_fr, _, _, hin1, hcsr1,
    hsh1, hbuf1, hedge1, L, hL_env, hL_es, hL_eb, hL_max, hL_off, hL_adj, hL_it, hL_nd, hL_bf, _⟩
  have hm3 : L.es.length = 3 := by rw [hL_es]; rfl
  have hs1_fr' : s1.frontier = L.bufBase + (14 * 3 + 14 * L.es.length) := by
    simpa [s1, s0, esK3, hL_bf, hm3] using hs1_fr
  have hsh_eq' : setup.sh =
      ⟨setup.sh.itemBase, setup.sh.nodeBase, 0, 0, 0, partRankThreshold⟩ := by
    simpa [setup, s0, esK3] using hsh_eq
  have hib_eq' : setup.sh.itemBase = L.itemBase := by
    simpa [setup, s0, esK3] using hL_it.symm
  have hnb_eq' : setup.sh.nodeBase = L.nodeBase := by
    simpa [setup, s0, esK3] using hL_nd.symm
  have hsh1' : SHInv 16 setup.sh.itemCount setup.sh.nodeCount (2 * L.es.length) (4 * L.es.length)
      setup.sh [] (fun _ => 0) s1 := by
    have hsh1_0 := hsh1
    rw [hsh_eq] at hsh1_0
    rw [hsh_eq', hm3]
    simpa [setup, s1, s0, esK3] using hsh1_0
  have hcsr1' : HoldsUndirCSR L.offBase L.adjBase L.es s1.mem := by
    simpa [s1, s0, esK3, hL_off, hL_adj, hL_es] using hcsr1
  have hin1' : HoldsIndexedEdges L.edgeBase L.es s1.mem := by
    simpa [s1, s0, esK3, hL_eb, hL_es] using hin1
  have hbuf1' : ∀ j < 6, s1.mem (L.bufBase + j) = 0 := by
    simpa [s1, s0, esK3, hL_bf] using hbuf1
  have hedge1' : ∀ j < L.es.length, s1.mem (L.bufBase + 14 * 3 + j) = 0 := by
    simpa [s1, s0, esK3, hL_bf, hm3] using hedge1
  have hrem0 : remDeg 3 L.offBase s1.mem (Finset.univ.filter fun x : Fin 3 => (0 : ℕ) ≠ 0) = 6 := by
    simpa [hm3] using remDeg_empty hcsr1'
  have hic0 : setup.sh.itemCount = 0 := by rw [hsh_eq']
  have hrun := partRunRound_spec L s1 (fun _ => 0) (fun _ => 0) (fun _ => 0) 0 0 0 0 0
    ⟨0, by decide⟩ setup.sh hs1_fr' hib_eq' hnb_eq'
    (by rw [hsh_eq']) (by rw [hsh_eq']; exact Nat.zero_le _) hsh1' hcsr1' hin1'
    (fun x hx => hbuf1' x (by omega))
    (fun x hx => by rw [Nat.add_assoc]; exact hbuf1' (3 + x) (by omega))
    (fun _ _ => Nat.zero_le _) rfl hedge1'
    (by rw [hL_es]; exact isSimple_esK3) (by simp) (by simp) (by simp) (by simp)
    (by rw [hic0, hrem0, hm3])
  rcases hrun with ⟨_, hvh_r, _, _, _, _, _, _, _, _, _, _, _, _, _, hsh_r, hmc_diff, _,
    r, emIdx, corrIdx, treeIdx, _, _, htr_len, _, _, _,
    hnd_em, _, _, _, hcr_len, _, _, hcg_eq, _, _,
    _, _, _, _, _, hu_in, hcard_nv, _, _, _, _, hcomp_simp,
    _, _, _, _, _, _, hemit_iff, _,
    _, _, _, _, _, hcross, _, _, _⟩
  have hcorr_nil : corrIdx = [] := List.eq_nil_of_length_eq_zero (by
    have hsh_ic := hsh_r.ic_max
    have h1 := hmc_diff
    rw [hsh_eq'] at h1
    rw [hm3] at hsh_ic
    have h2 := hcr_len
    dsimp only [st0] at h1 h2; omega)
  have hcard_le3 : r.verts.card ≤ 3 := by simpa [Fintype.card_fin] using Finset.card_le_univ r.verts
  have hno_cross : ∀ eIdx : Fin L.es.length,
      ¬((L.es[eIdx.val]'eIdx.isLt).u ∈ r.verts ↔ (L.es[eIdx.val]'eIdx.isLt).v ∉ r.verts) := by
    rcases hcross with hmax | ⟨x, hx⟩ | hnc
    · rw [hL_max] at hmax; omega
    · simp at hx
    · exact fun eIdx => hnc eIdx rfl
  have h0 : (⟨0, by decide⟩ : Fin 3) ∈ r.verts := hu_in
  have h1 : (⟨1, by decide⟩ : Fin 3) ∈ r.verts := by
    have hc := hno_cross ⟨0, by rw [hm3]; decide⟩
    simp only [hL_es, esK3, List.getElem_cons_zero] at hc
    by_contra hnot; exact hc ⟨fun _ => hnot, fun _ => h0⟩
  have h2 : (⟨2, by decide⟩ : Fin 3) ∈ r.verts := by
    have hc := hno_cross ⟨1, by rw [hm3]; decide⟩
    simp only [hL_es, esK3, List.getElem_cons_succ, List.getElem_cons_zero] at hc
    by_contra hnot; exact hc ⟨fun _ => hnot, fun _ => h1⟩
  have huniv : r.verts = Finset.univ := by
    ext x; refine ⟨fun _ => Finset.mem_univ _, fun _ => ?_⟩
    fin_cases x <;> assumption
  have hnv3 : r.numVerts = 3 := by rw [← hcard_nv, huniv, Finset.card_fin]
  have hsteps2 : r.tree.numSteps = 2 := by
    have hdc := djpVerts_card r.tree r.tree.numSteps le_rfl
    change r.verts.card = r.tree.numSteps + 1 at hdc
    rw [huniv, Finset.card_fin] at hdc; omega
  have hem_all : ∀ i : Fin L.es.length, i ∈ emIdx := fun i =>
    (hemit_iff i).mpr ⟨rfl, huniv ▸ Finset.mem_univ _, huniv ▸ Finset.mem_univ _⟩
  have hperm_fin : emIdx.Perm (List.finRange L.es.length) :=
    (List.perm_ext_iff_of_nodup hnd_em (List.nodup_finRange _)).mpr fun i =>
      ⟨fun _ => List.mem_finRange i, fun _ => hem_all i⟩
  have hcg_perm : r.compGlobal.Perm esK3 := by
    rw [hcg_eq]
    have hm := hperm_fin.map fun eIdx : Fin L.es.length => L.es[eIdx.val]'eIdx.isLt
    have hmap_es : (List.finRange L.es.length).map (fun eIdx : Fin L.es.length =>
        L.es[eIdx.val]'eIdx.isLt) = L.es := by
      refine List.ext_getElem (by simp) fun i hi _ => by simp
    rw [hmap_es] at hm
    simpa [hL_es] using hm
  have hspec := partitionProg_spec (by decide) hinit.1 (maxsize := 4) (by decide) hinit.2.2
    (by rw [hinit.2.1]; decide) (by rw [hinit.2.1]; decide) isSimple_esK3
  rcases hspec with ⟨hsafe_p, hvh_p, _, _, _, _, _, hnc_le, hmc_le, _, _, _, _, _, _, _, _,
    rounds, H_rem, conglomFn, hrl, _, _, hperm_p, _, _, _, _, _, _, hcov_p, hmeta_p, _, _, _, _, _⟩
  have hmc0 : rProg.1.mcLen = 0 :=
    Nat.eq_zero_of_le_zero (by simpa [rProg, execWordRAM, s0, esK3] using hmc_le)
  have h1_le : 1 ≤ rProg.1.numComps := by
    obtain ⟨q, hq, _⟩ := hcov_p ⟨0, by decide⟩
    exact Nat.succ_le_of_lt (by
      simpa [rProg, execWordRAM, s0, esK3, hrl] using List.length_pos_of_mem hq)
  have hopt := partition_optDepth_sum_le isSimple_esK3 (subperm_compGlobal_of_perm hperm_p)
    fun i => ⟨hmeta_p.lift_injective i, hmeta_p.compGlobal_verts i,
      hmeta_p.inter_prev_card_le_one i⟩
  have hL_env' : L.toEnv = setup.env := by simpa [setup, s0, esK3] using hL_env
  refine ⟨by dsimp only [prog]; rw [← hL_env']; exact hvh_r,
    ⟨r, corrIdx.map (Fin.cast hm3), hnv3, huniv, by simp [hcorr_nil], hcg_perm, hsteps2⟩,
    by simpa [s0, esK3] using hsafe_p, by simpa [s0, esK3] using hvh_p,
    hmc0, h1_le, by simpa [rProg, execWordRAM, s0, esK3] using hnc_le, rounds, hopt⟩

/-! ## 4. Overlapping Conglomerate on `K_3` (`maxsize = 2`) + Full `Bridges` Suite -/

-- Test (d): Two chained rounds of `partRunRound_spec` on `K_3` (`maxsize = 2`) producing
-- overlapping components merged into 1 conglomerate via `vOut`, plus `Bridges`
-- (`optDepth`, `conglom_active_verts_le`, `isMinSpanningForest`) and `partitionProg_spec`.
example :
    let s0 := mkInitState esK3
    let rProg := execWordRAM s0 (partitionProg ⟨3, 3, 0, 2⟩)
    (∃ (r0 r1 : PartitionRoundWitness 3) (H_rem : List (IndexedEdge 3))
        (conglomFn : Fin 3 → Fin 1) (F : List (WeightedEdge 3 ℕ)),
      r0.verts.card = 2 ∧
      r1.verts.card = 2 ∧
      (r1.verts ∩ r0.verts).Nonempty ∧
      (∃ x ∈ r1.verts ∩ r0.verts, ∃ hpos : 0 < r1.tree.numSteps,
        x = r1.tree.vOut ⟨r1.tree.numSteps - 1, Nat.sub_lt hpos Nat.one_pos⟩) ∧
      (([r0, r1].flatMap PartitionRoundWitness.compGlobal) ++ H_rem ++
        ([r0, r1].flatMap PartitionRoundWitness.corrEdges)).Perm esK3 ∧
      (∀ x y : Fin 3, conglomFn x = conglomFn y ↔
        (edgePartition ([r0, r1].flatMap fun q => q.tree.treeEdges)).rel x y = true) ∧
      (([r0, r1]).map fun q =>
        optDepth (edgeEnds (q.compLocal.map IndexedEdge.toWeighted))).sum ≤
        optDepthMN 3 3 ∧
      1 * 2 ≤ 3 ∧
      IsMinSpanningForest (esK3.map IndexedEdge.toWeighted) F) ∧
    partitionProgSafe 16 ⟨3, 3, 0, 2⟩ s0 ∧
    2 ≤ rProg.1.numComps ∧ rProg.1.numComps ≤ 3 ∧ rProg.1.mcLen = 0 := by
  intro s0 rProg
  have hinit := mkInitState_spec (w := 16) esK3 (by decide) (by decide)
    (fun e he => by simp only [esK3, List.mem_cons, List.not_mem_nil, or_false] at he
                    rcases he with rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩)
  have hsetup := partSetup_spec (w := 16) (n := 3) (edgeBase := 0) (maxsize := 2) (by decide)
    hinit.1 (by decide) (by decide) hinit.2.2 (by rw [hinit.2.1]; decide)
    (by rw [hinit.2.1]; decide)
  rcases hsetup with ⟨_, _, _, _, hm, _, hmax, _, hsh_eq, hs1_fr, _, _, hin1, hcsr1,
    hsh1, hbuf1, hedge1, L, hL_env, hL_es, hL_eb, hL_max, hL_off, hL_adj, hL_it, hL_nd, hL_bf, _⟩
  let s1 := (Memory.spec 0).clientState s0 (partSetup ⟨3, 3, 0, 2⟩)
  let setup := (Memory.spec 0).clientResult s0 (partSetup ⟨3, 3, 0, 2⟩)
  have hm3 : L.es.length = 3 := by rw [hL_es]; rfl
  have hs1_fr' : s1.frontier = L.bufBase + (14 * 3 + 14 * L.es.length) := by
    simpa [s1, s0, esK3, hL_bf, hm3] using hs1_fr
  have hsh_eq' : setup.sh =
      ⟨setup.sh.itemBase, setup.sh.nodeBase, 0, 0, 0, partRankThreshold⟩ := by
    simpa [setup, s0, esK3] using hsh_eq
  have hib_eq' : setup.sh.itemBase = L.itemBase := by
    simpa [setup, s0, esK3] using hL_it.symm
  have hnb_eq' : setup.sh.nodeBase = L.nodeBase := by
    simpa [setup, s0, esK3] using hL_nd.symm
  have hsh1' : SHInv 16 setup.sh.itemCount setup.sh.nodeCount (2 * L.es.length) (4 * L.es.length)
      setup.sh [] (fun _ => 0) s1 := by
    have hsh1_0 := hsh1
    rw [hsh_eq] at hsh1_0
    rw [hsh_eq', hm3]
    simpa [setup, s1, s0, esK3] using hsh1_0
  have hcsr1' : HoldsUndirCSR L.offBase L.adjBase L.es s1.mem := by
    simpa [s1, s0, esK3, hL_off, hL_adj, hL_es] using hcsr1
  have hin1' : HoldsIndexedEdges L.edgeBase L.es s1.mem := by
    simpa [s1, s0, esK3, hL_eb, hL_es] using hin1
  have hbuf1' : ∀ j < 6, s1.mem (L.bufBase + j) = 0 := by
    simpa [s1, s0, esK3, hL_bf] using hbuf1
  have hedge1' : ∀ j < L.es.length, s1.mem (L.bufBase + 14 * 3 + j) = 0 := by
    simpa [s1, s0, esK3, hL_bf, hm3] using hedge1
  have hrem0 : remDeg 3 L.offBase s1.mem (Finset.univ.filter fun x : Fin 3 => (0 : ℕ) ≠ 0) = 6 := by
    simpa [hm3] using remDeg_empty hcsr1'
  -- Round 0 from vertex 0
  let st0 : PartOuterState := ⟨0, 0, 0, 0, 0, 0, setup.sh⟩
  have hic0 : setup.sh.itemCount = 0 := by rw [hsh_eq']
  have hrun0 := partRunRound_spec L s1 (fun _ => 0) (fun _ => 0) (fun _ => 0) 0 0 0 0 0
    ⟨0, by decide⟩ setup.sh hs1_fr' hib_eq' hnb_eq'
    (by rw [hsh_eq']) (by rw [hsh_eq']; exact Nat.zero_le _) hsh1' hcsr1' hin1'
    (fun x hx => hbuf1' x (by omega))
    (fun x hx => by rw [Nat.add_assoc]; exact hbuf1' (3 + x) (by omega))
    (fun _ _ => Nat.zero_le _) rfl hedge1'
    (by rw [hL_es]; exact isSimple_esK3) (by simp) (by simp) (by simp) (by simp)
    (by rw [hic0, hrem0, hm3])
  let res1 := (Memory.spec 0).clientResult s1 (partRunRound (L.toEnv, st0))
  let s2 := (Memory.spec 0).clientState s1 (partRunRound (L.toEnv, st0))
  rcases hrun0 with ⟨_, _, _, _, hce0_le, hmc0_le, hs2_fr, _, hmod0,
    hib1, hnb1, hfr1, hrt1, hic1_ge, hnc1_le, hsh2, hmc0_diff, hclaim0,
    r0, em0, corr0, treeIdx0, hcl0_eq, htl0_eq, htr0_len, htr0_w, htr0_src, _,
    hnd_em0, hnd_cr0, hdisj0, hcp0_len, hcr0_len, hcr0_eq, _, hcg0_eq, _, _,
    _, _, _, _, hroot0, hu0_in, hcard0_eq, hnv0_pos, hnv0_max, _, hinj0, hcp0_simp,
    hcg0_verts, htr0_sub, hdead0_fn, hincur0_in, hincur0_out, hest0_fn, hemit0_iff, hcr0_es,
    htlen0_dead, hcl0_dead, hnc0_dead, hcap0_rem, _, hcross0, huncorr0, hprev0, _⟩
  have hres1_mc : corr0.length = res1.mcLen := by simpa [res1, st0] using hcr0_len
  have hmc0_le' : 16 * res1.mcLen ≤ res1.sh.itemCount := by
    simpa [res1, st0, hic0] using hmc0_diff
  have hs2_fr' : s2.frontier = s1.frontier := by simpa [s2, st0] using hs2_fr
  have hib1' : res1.sh.itemBase = L.itemBase := by simpa [res1, st0] using hib1
  have hnb1' : res1.sh.nodeBase = L.nodeBase := by simpa [res1, st0] using hnb1
  have hfr1' : res1.sh.firstRoot = 0 := by simpa [res1, st0] using hfr1
  have hrt1' : res1.sh.rankThreshold = partRankThreshold := by simpa [res1, st0] using hrt1
  have hnc1_le' : res1.sh.nodeCount ≤ 2 * res1.sh.itemCount := by simpa [res1, st0] using hnc1_le
  have hsh2' : SHInv 16 res1.sh.itemCount res1.sh.nodeCount (2 * L.es.length) (4 * L.es.length)
      res1.sh [] (fun _ => 0) s2 := by simpa [res1, s2, st0] using hsh2
  have hclaim0' : res1.cEdgeLen + res1.mcLen ≤
      (Finset.univ.filter fun i : Fin L.es.length =>
        s2.mem (L.bufBase + 14 * 3 + i.val) ≠ 0).card := by
    simpa [res1, s2, st0] using hclaim0
  have htlen0_dead' : res1.tLen ≤
      (Finset.univ.filter fun x : Fin 3 => s2.mem (L.bufBase + x.val) ≠ 0).card := by
    simpa [res1, s2, st0] using htlen0_dead
  have hcl0_dead' : res1.cLiftLen ≤
      (Finset.univ.filter fun x : Fin 3 => s2.mem (L.bufBase + x.val) ≠ 0).card + 1 := by
    simpa [res1, s2, st0] using hcl0_dead
  have hcap0_rem' : res1.sh.itemCount + remDeg 3 L.offBase s2.mem
      (Finset.univ.filter fun x : Fin 3 => s2.mem (L.bufBase + x.val) ≠ 0) ≤ 2 * L.es.length := by
    simpa [res1, s2, st0] using hcap0_rem
  have hdead0_fn' : ∀ x : Fin 3, s2.mem (L.bufBase + x.val) = if x ∈ r0.verts then 1 else 0 := by
    simpa [s2, st0] using hdead0_fn
  have hincur0_in' : ∀ x : Fin 3, x ∈ r0.verts → s2.mem (L.bufBase + 3 + x.val) = 1 := by
    simpa [s2, st0] using hincur0_in
  have hincur0_out' : ∀ x : Fin 3, x ∉ r0.verts → s2.mem (L.bufBase + 3 + x.val) = 0 := by
    intro x hx; simpa [s2, st0] using hincur0_out x hx
  have hest0_fn' : ∀ i < L.es.length, s2.mem (L.bufBase + 14 * 3 + i) =
      if ∃ hlt : i < L.es.length, (⟨i, hlt⟩ : Fin L.es.length) ∈ em0 then 1
      else if ∃ hlt : i < L.es.length, (⟨i, hlt⟩ : Fin L.es.length) ∈ corr0 then 2
      else 0 := by
    simpa [s2, st0] using hest0_fn
  have hmod0' : ∀ x, s2.mem x ≠ s1.mem x →
      InSHPool 0 0 (2 * L.es.length) (4 * L.es.length)
        ⟨L.itemBase, L.nodeBase, 0, 0, 0, partRankThreshold⟩ x ∨
      (L.bufBase ≤ x ∧ x < L.bufBase + 4 * 3) ∨
      (L.bufBase + 4 * 3 + 0 ≤ x ∧ x < L.bufBase + 4 * 3 + res1.cLiftLen) ∨
      (L.bufBase + 6 * 3 + 3 * 0 ≤ x ∧ x < L.bufBase + 6 * 3 + 3 * 1) ∨
      x = L.bufBase + 9 * 3 + 0 ∨
      (L.bufBase + 10 * 3 + 4 * 0 ≤ x ∧ x < L.bufBase + 10 * 3 + 4 * res1.tLen) ∨
      (L.bufBase + 14 * 3 ≤ x ∧ x < L.bufBase + 14 * 3 + 2 * L.es.length) ∨
      (L.bufBase + 14 * 3 + 2 * L.es.length + 4 * 0 ≤ x ∧
        x < L.bufBase + 14 * 3 + 2 * L.es.length + 4 * res1.cEdgeLen) ∨
      (L.bufBase + 14 * 3 + 6 * L.es.length + 4 * 0 ≤ x ∧
        x < L.bufBase + 14 * 3 + 6 * L.es.length + 4 * res1.mcLen) := by
    simpa [res1, s2, st0] using hmod0
  have hm_eq0 : L.es.length = 3 := hm3
  have hr0_card_le2 : r0.verts.card ≤ 2 := by rw [hcard0_eq]; exact hL_max ▸ hnv0_max
  have hcorr0_nil : corr0 = [] := List.eq_nil_of_length_eq_zero (by
    have hic_max := hsh2'.ic_max
    rw [hm3] at hic_max
    omega)
  have hr0_card_eq2 : r0.verts.card = 2 := by
    rcases hcross0 with hge2 | ⟨x, hx⟩ | hnc
    · rw [hL_max] at hge2; omega
    · simp at hx
    · have hcard_lt : r0.verts.card < 2 → False := fun hlt => by
        have h1 : r0.verts.card = 1 := by
          have : 1 ≤ r0.verts.card := Finset.card_pos.mpr ⟨_, hu0_in⟩; omega
        have heq0 : r0.verts = {⟨0, by decide⟩} :=
          (Finset.eq_singleton_iff_unique_mem.mpr ⟨hu0_in, fun y hy => by
            by_contra hne
            have h2c : ({⟨0, by decide⟩, y} : Finset (Fin 3)).card ≤ r0.verts.card :=
              Finset.card_le_card
                (Finset.insert_subset_iff.mpr ⟨hu0_in, Finset.singleton_subset_iff.mpr hy⟩)
            rw [Finset.card_pair (Ne.symm hne)] at h2c; omega⟩)
        have hce := hnc ⟨0, by rw [hm3]; decide⟩ rfl
        rw [heq0] at hce
        simp [hL_es, esK3] at hce
      by_contra hne; exact hcard_lt (by omega)
  -- Pick the unique vertex u1 outside r0.verts
  have hu1_ex : (Finset.univ \ r0.verts).Nonempty := by
    rw [← Finset.card_pos, Finset.card_sdiff, Finset.inter_univ, Finset.card_fin, hr0_card_eq2]
    decide
  let u1 := hu1_ex.choose
  have hu1_not : u1 ∉ r0.verts := (Finset.mem_sdiff.mp hu1_ex.choose_spec).2
  have hs2_below : ∀ x < L.itemBase, s2.mem x = s1.mem x := fun x hx => by
    by_contra hne
    rcases hmod0' x hne with hp | h | h | h | h | h | h | h | h
    · exact absurd (L.inSHPool_lt_bufBase rfl rfl hp).1 (not_le_of_gt hx)
    all_goals (have := L.hit_nd; have := L.hnd_buf; omega)
  have hin2 := (L.congr_below_itemBase hs2_below).1 hin1'
  have hcsr2 := (L.congr_below_itemBase hs2_below).2 hcsr1'
  have hdeadSet1 : (Finset.univ.filter fun x : Fin 3 => s2.mem (L.bufBase + x.val) ≠ 0) =
      r0.verts := by
    ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, hdead0_fn' x]
    by_cases hx : x ∈ r0.verts <;> simp [hx]
  -- Round 1 from vertex u1
  have hrun1 := partRunRound_spec L s2 (fun x => s2.mem (L.bufBase + x))
    (fun x => s2.mem (L.bufBase + 3 + x)) (fun i => s2.mem (L.bufBase + 14 * 3 + i))
    1 res1.cEdgeLen res1.cLiftLen res1.mcLen res1.tLen u1 res1.sh
    (by rw [hs2_fr', hs1_fr', hm3]) hib1' hnb1' hrt1' hnc1_le' hsh2' hcsr2 hin2
    (fun _ _ => rfl) (fun _ _ => rfl)
    (fun x hx => by
      by_cases hxr : (⟨x, hx⟩ : Fin 3) ∈ r0.verts
      · simp [hincur0_in' ⟨x, hx⟩ hxr]
      · rw [hincur0_out' ⟨x, hx⟩ hxr]; exact Nat.zero_le 1)
    (by simp [hdead0_fn' u1, hu1_not])
    (fun _ _ => rfl) (by rw [hL_es]; exact isSimple_esK3)
    (by rw [hdeadSet1, hr0_card_eq2]; decide)
    (by simpa [hm3, ← hdeadSet1] using htlen0_dead')
    (by simpa [hm3, ← hdeadSet1] using hcl0_dead')
    (by simpa [hm3] using hclaim0')
    (by simpa [hm3, ← hdeadSet1] using hcap0_rem')
  let st1_r1 : PartOuterState :=
    ⟨u1.val, 1, res1.cEdgeLen, res1.cLiftLen, res1.mcLen, res1.tLen, res1.sh⟩
  let res2 := (Memory.spec 0).clientResult s2 (partRunRound (L.toEnv, st1_r1))
  rcases hrun1 with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hic1_ge_2, _, hsh3, hmc1_diff, _,
    r1, em1, corr1, treeIdx1, _, _, htr1_len, htr1_w, htr1_src, _,
    hnd_em1, _, _, hcp1_len, hcr1_len, hcr1_eq, _, hcg1_eq, _, _,
    _, _, _, _, _, hu1_in, hcard1_eq, _, hnv1_max, _, hinj1, hcp1_simp,
    hcg1_verts, htr1_sub, _, _, _, _, hemit1_iff, _,
    _, _, _, _, hdead_inter1, hcross1, huncorr1, hprev1, _⟩
  have hcorr1_nil : corr1 = [] := List.eq_nil_of_length_eq_zero (by
    have hic_max : res2.sh.itemCount ≤ 2 * L.es.length := by
      simpa [res2, st1_r1] using hsh3.ic_max
    have hmc_diff1 : 16 * (res2.mcLen - res1.mcLen) ≤ res2.sh.itemCount - res1.sh.itemCount := by
      simpa [res2, st1_r1] using hmc1_diff
    have hcr1_len' : corr1.length = res2.mcLen - res1.mcLen := by
      simpa [res2, st1_r1] using hcr1_len
    have hmc0_eq : res1.mcLen = 0 := by rw [← hres1_mc, hcorr0_nil]; rfl
    rw [hm3] at hic_max
    omega)
  have hinter1_ne : (r1.verts ∩ r0.verts).Nonempty := by
    rcases hcross1 with hge2 | ⟨x, hx⟩ | hnc
    · have hle2 : r1.verts.card ≤ 2 := by rw [hcard1_eq]; exact hL_max ▸ hnv1_max
      have hcard_eq : r1.verts.card = 2 := le_antisymm hle2 (hL_max ▸ hge2)
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      have hdisj : Disjoint r1.verts r0.verts := Finset.disjoint_iff_inter_eq_empty.mpr hempty
      have hun_card := Finset.card_union_of_disjoint hdisj
      rw [hcard_eq, hr0_card_eq2] at hun_card
      have hle3 := Finset.card_le_univ (r1.verts ∪ r0.verts)
      rw [Fintype.card_fin] at hle3; omega
    · exact ⟨x, by simpa [hdeadSet1] using hx⟩
    · by_contra hempty
      have hz_ex : r0.verts.Nonempty := Finset.card_pos.mp (by rw [hr0_card_eq2]; decide)
      obtain ⟨z, hz⟩ := hz_ex
      have hne_uz : u1 ≠ z := fun h => hu1_not (h ▸ hz)
      have he_ex : ∃ eIdx : Fin L.es.length,
          ((L.es[eIdx.val]'eIdx.isLt).u = u1 ∧ (L.es[eIdx.val]'eIdx.isLt).v = z) ∨
          ((L.es[eIdx.val]'eIdx.isLt).u = z ∧ (L.es[eIdx.val]'eIdx.isLt).v = u1) := by
        obtain ⟨e0, he0⟩ := esK3_edge_between hne_uz
        refine ⟨⟨e0.val, hm3.symm ▸ e0.isLt⟩, ?_⟩
        have hL0 : L.es[e0.val]'(hm3.symm ▸ e0.isLt) = esK3[e0.val]'e0.isLt :=
          (fun h1 h2 => by simp [hL_es] : ∀ h1 h2, L.es[e0.val]'h1 = esK3[e0.val]'h2) _ _
        rw [hL0]; exact he0
      obtain ⟨eIdx, huv⟩ := he_ex
      have hnot_em0 : eIdx ∉ em0 := by
        intro hin
        have hmem := ((hemit0_iff eIdx).mp hin).2
        rcases huv with ⟨hu, hv⟩ | ⟨hu, hv⟩
        · exact hu1_not (hu ▸ hmem.1)
        · exact hu1_not (hv ▸ hmem.2)
      have hnot_cr0 : eIdx ∉ corr0 := by simp [hcorr0_nil]
      have hes1 : s2.mem (L.bufBase + 14 * 3 + eIdx.val) = 0 := by
        rw [hest0_fn' eIdx.val eIdx.isLt]
        have hnot1 : ¬∃ hlt : eIdx.val < L.es.length, (⟨eIdx.val, hlt⟩ : Fin L.es.length) ∈ em0 :=
          fun ⟨_, hm⟩ => hnot_em0 hm
        have hnot2 : ¬∃ hlt : eIdx.val < L.es.length,
            (⟨eIdx.val, hlt⟩ : Fin L.es.length) ∈ corr0 :=
          fun ⟨_, hm⟩ => hnot_cr0 hm
        simp only [hnot1, hnot2, ↓reduceIte]
      have hcross_e := hnc eIdx hes1
      have hdisj : Disjoint r1.verts r0.verts := Finset.disjoint_iff_inter_eq_empty.mpr
        (Finset.not_nonempty_iff_eq_empty.mp hempty)
      have hz_not1 : z ∉ r1.verts := Finset.disjoint_right.mp hdisj hz
      rcases huv with ⟨hu, hv⟩ | ⟨hu, hv⟩
      · exact hcross_e (iff_of_true (hu ▸ hu1_in) (hv ▸ hz_not1))
      · exact hcross_e (iff_of_false (hu ▸ hz_not1) (not_not.mpr (hv ▸ hu1_in)))
  have hstop_some1 : ∃ x ∈ r1.verts ∩ r0.verts, ∃ hpos : 0 < r1.tree.numSteps,
      x = r1.tree.vOut ⟨r1.tree.numSteps - 1, Nat.sub_lt hpos Nat.one_pos⟩ := by
    obtain ⟨x, hx⟩ := hinter1_ne
    exact ⟨x, hx, hprev1 x (Finset.mem_inter.mp hx).1 (by
      simpa [hdeadSet1] using (Finset.mem_inter.mp hx).2)⟩
  have hr1_card_eq2 : r1.verts.card = 2 := by
    have hle2 : r1.verts.card ≤ 2 := by rw [hcard1_eq]; exact hL_max ▸ hnv1_max
    obtain ⟨x, hx⟩ := hinter1_ne
    rw [Finset.mem_inter] at hx
    have hne_xu : x ≠ u1 := fun h => hu1_not (h ▸ hx.2)
    have hge2 : 2 ≤ r1.verts.card := by
      have h2 := Finset.card_le_card
        (Finset.insert_subset_iff.mpr ⟨hx.1, Finset.singleton_subset_iff.mpr hu1_in⟩)
      rwa [Finset.card_pair hne_xu] at h2
    exact le_antisymm hle2 hge2
  -- Build Bridges arguments for [r0, r1]
  let rounds : List (PartitionRoundWitness 3) := [r0, r1]
  have heq_rounds : rounds = [r0, r1] := rfl
  let em0' : List (Fin 3) := em0.map (Fin.cast hm3)
  let em1' : List (Fin 3) := em1.map (Fin.cast hm3)
  let remIdx : List (Fin 3) := (List.finRange 3).filter fun i => decide (i ∉ em0' ∧ i ∉ em1')
  let H_rem : List (IndexedEdge 3) := remIdx.map fun i => esK3[i.val]'i.isLt
  have hcast_es : ∀ (i : ℕ) (hi1 : i < L.es.length) (hi2 : i < esK3.length),
      L.es[i]'hi1 = esK3[i]'hi2 := fun i hi1 hi2 => by simp [hL_es]
  have hm_esK3 : L.es.length = esK3.length := congrArg List.length hL_es
  have hem0_eq : r0.compGlobal = em0'.map fun i => esK3[i.val]'i.isLt := by
    rw [hcg0_eq]; dsimp only [em0']; rw [List.map_map]
    exact List.map_congr_left fun a _ => hcast_es a.val a.isLt (hm_esK3 ▸ a.isLt)
  have hem1_eq : r1.compGlobal = em1'.map fun i => esK3[i.val]'i.isLt := by
    rw [hcg1_eq]; dsimp only [em1']; rw [List.map_map]
    exact List.map_congr_left fun a _ => hcast_es a.val a.isLt (hm_esK3 ▸ a.isLt)
  have hnd_em0' : em0'.Nodup :=
    hnd_em0.map fun {a b} hab => Fin.ext (congrArg (Fin.val : Fin 3 → ℕ) hab)
  have hnd_em1' : em1'.Nodup :=
    hnd_em1.map fun {a b} hab => Fin.ext (congrArg (Fin.val : Fin 3 → ℕ) hab)
  have hdisj_em01 : ∀ i ∈ em0', i ∉ em1' := fun i hi0 hi1 => by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hi0
    obtain ⟨b, hb, hab⟩ := List.mem_map.mp hi1
    have hval : a.val = b.val := (congrArg Fin.val hab).symm
    have hes1 := ((hemit1_iff b).mp hb).1
    rw [← hval, hest0_fn' a.val a.isLt] at hes1
    have hex : ∃ hlt : a.val < L.es.length, (⟨a.val, hlt⟩ : Fin L.es.length) ∈ em0 :=
      ⟨a.isLt, ha⟩
    simp only [hex, ↓reduceIte] at hes1; omega
  have hnd_all : (em0' ++ em1' ++ remIdx).Nodup := by
    rw [List.nodup_append, List.nodup_append]
    refine ⟨⟨hnd_em0', hnd_em1', fun i hi0 j hj1 hij => hdisj_em01 i hi0 (hij ▸ hj1)⟩,
      (List.nodup_finRange 3).filter _, fun i hi j hj hij => ?_⟩
    subst hij
    have hf := (List.mem_filter.mp hj).2
    simp only [decide_eq_true_eq] at hf
    rcases List.mem_append.mp hi with h | h
    · exact hf.1 h
    · exact hf.2 h
  have hperm_fin3 : (em0' ++ em1' ++ remIdx).Perm (List.finRange 3) :=
    (List.perm_ext_iff_of_nodup hnd_all (List.nodup_finRange 3)).mpr fun i => by
      refine ⟨fun _ => List.mem_finRange i, fun _ => ?_⟩
      by_cases h0 : i ∈ em0'
      · exact List.mem_append_left _ (List.mem_append_left _ h0)
      · by_cases h1 : i ∈ em1'
        · exact List.mem_append_left _ (List.mem_append_right _ h1)
        · exact List.mem_append_right _
            (List.mem_filter.mpr ⟨List.mem_finRange i, by simp [h0, h1]⟩)
  have hperm_r : ((rounds.flatMap PartitionRoundWitness.compGlobal) ++ H_rem ++
      (rounds.flatMap PartitionRoundWitness.corrEdges)).Perm esK3 := by
    have hcr_nil : rounds.flatMap PartitionRoundWitness.corrEdges = [] := by
      simp [rounds, hcr0_eq, hcr1_eq, hcorr0_nil, hcorr1_nil]
    rw [hcr_nil, List.append_nil, List.flatMap_cons, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, hem0_eq, hem1_eq]
    have hmap_all : (em0'.map (fun i => esK3[i.val]'i.isLt)) ++
        (em1'.map (fun i => esK3[i.val]'i.isLt)) ++
        (remIdx.map (fun i => esK3[i.val]'i.isLt)) =
        (em0' ++ em1' ++ remIdx).map (fun i => esK3[i.val]'i.isLt) := by
      rw [List.map_append, List.map_append]
    have hmap_esK3 : (List.finRange 3).map (fun i : Fin 3 => esK3[i.val]'i.isLt) = esK3 := by
      refine List.ext_getElem (by simp [esK3]) fun i hi _ => by simp [esK3]
    rw [hmap_all]
    simpa [hmap_esK3] using hperm_fin3.map fun i : Fin 3 => esK3[i.val]'i.isLt
  have hcov_r : ∀ x : Fin 3, ∃ q ∈ rounds, x ∈ q.verts := fun x => by
    by_cases hx : x ∈ r0.verts
    · exact ⟨r0, by simp [rounds], hx⟩
    · have hcard_sdiff : (Finset.univ \ r0.verts).card = 1 := by
        rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_fin, hr0_card_eq2]
      have hx_eq : x = u1 := by
        have hx_sd : x ∈ Finset.univ \ r0.verts := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hx⟩
        have hu_sd : u1 ∈ Finset.univ \ r0.verts :=
          Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hu1_not⟩
        exact Finset.card_le_one.mp hcard_sdiff.le x hx_sd u1 hu_sd
      exact ⟨r1, by simp [rounds], hx_eq ▸ hu1_in⟩
  let conglomFn : Fin 3 → Fin 1 := fun _ => 0
  have hrel_conglom : ∀ x y : Fin 3, conglomFn x = conglomFn y ↔
      (edgePartition (rounds.flatMap fun q => q.tree.treeEdges)).rel x y = true := by
    intro x y; refine ⟨fun _ => ?_, fun _ => Subsingleton.elim _ _⟩
    let E := rounds.flatMap fun q => q.tree.treeEdges
    have hsub0 : r0.tree.treeEdges.Subperm E := by
      simp only [E, rounds, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      exact (List.sublist_append_left _ _).subperm
    have hsub1 : r1.tree.treeEdges.Subperm E := by
      simp only [E, rounds, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      exact (List.sublist_append_right _ _).subperm
    obtain ⟨w_sh, hw_sh⟩ := hinter1_ne
    rw [Finset.mem_inter] at hw_sh
    have hbridge : (edgePartition E).rel r0.tree.root r1.tree.root = true :=
      (edgePartition E).trans (edgePartition_root_rel_mem hsub0 hw_sh.2)
        ((edgePartition E).symm (edgePartition_root_rel_mem hsub1 hw_sh.1))
    have hx_root : (edgePartition E).rel x r0.tree.root = true := by
      rcases hcov_r x with ⟨q, hq, hxq⟩
      simp only [rounds, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact (edgePartition E).symm (edgePartition_root_rel_mem hsub0 hxq)
      · exact (edgePartition E).trans
          ((edgePartition E).symm (edgePartition_root_rel_mem hsub1 hxq))
          ((edgePartition E).symm hbridge)
    have hy_root : (edgePartition E).rel r0.tree.root y = true := by
      rcases hcov_r y with ⟨q, hq, hyq⟩
      simp only [rounds, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact edgePartition_root_rel_mem hsub0 hyq
      · exact (edgePartition E).trans hbridge (edgePartition_root_rel_mem hsub1 hyq)
    exact (edgePartition E).trans hx_root hy_root
  have hopt_d := partition_optDepth_sum_le isSimple_esK3 (subperm_compGlobal_of_perm hperm_r)
    fun i => by
      fin_cases i
      · exact ⟨hinj0, hcg0_verts, by simp [heq_rounds]⟩
      · refine ⟨hinj1, hcg1_verts, ?_⟩
        dsimp only [rounds] at *; simp only [List.length_cons, List.length_nil, Nat.zero_add] at *
        have heq : (Finset.univ.filter fun j : Fin 2 => j.val < 1).biUnion
            (fun j => (([r0, r1] : List (PartitionRoundWitness 3))[j.val]'j.isLt).verts) =
            r0.verts := by
          ext z; simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨fun ⟨j, hj, hz⟩ => ?_, fun hz => ⟨⟨0, by decide⟩, by decide, hz⟩⟩
          rcases j with ⟨j, hj2⟩
          match j with
          | 0 => exact hz
          | 1 => simp at hj
        rw [heq]; simpa [hdeadSet1] using hdead_inter1
  have hact_d := partition_conglom_active_verts_le (n_a := 1) (lift_a := fun _ => (0 : Fin 1))
    hcov_r hrel_conglom (fun i => by
      fin_cases i
      · exact .inl (hL_max ▸ hr0_card_eq2.ge)
      · exact .inl (hL_max ▸ hr1_card_eq2.ge))
    (fun a b _ => Subsingleton.elim a b)
    (fun _ => by
      have hlen0 : r0.compGlobal.length ≤ 1 := by
        have hlen_map : r0.compGlobal.length = r0.compLocal.length := by
          simp [PartitionRoundWitness.compGlobal]
        exact hlen_map ▸ card_simple_fin2_le_one (by rw [← hcard0_eq, hr0_card_eq2]) hcp0_simp
      have hlen1 : r1.compGlobal.length ≤ 1 := by
        have hlen_map : r1.compGlobal.length = r1.compLocal.length := by
          simp [PartitionRoundWitness.compGlobal]
        exact hlen_map ▸ card_simple_fin2_le_one (by rw [← hcard1_eq, hr1_card_eq2]) hcp1_simp
      have hrem_pos : 0 < H_rem.length := by
        have hpl := hperm_r.length_eq
        have hcr_nil : rounds.flatMap PartitionRoundWitness.corrEdges = [] := by
          simp [rounds, hcr0_eq, hcr1_eq, hcorr0_nil, hcorr1_nil]
        rw [List.length_append, List.length_append, hcr_nil, List.length_nil,
          List.flatMap_cons, List.flatMap_cons, List.flatMap_nil, List.append_nil,
          List.length_append] at hpl
        simp [esK3] at hpl; omega
      obtain ⟨e_act, he_act⟩ := List.exists_mem_of_ne_nil H_rem (List.ne_nil_of_length_pos hrem_pos)
      exact ⟨e_act, he_act, .inl (Subsingleton.elim _ _)⟩)
  let F_comps : List (List (WeightedEdge 3 ℕ)) :=
    [kruskalEdges (r0.compGlobal.map IndexedEdge.toWeighted),
     kruskalEdges (r1.compGlobal.map IndexedEdge.toWeighted)]
  let F := kruskalEdges (F_comps.flatten ++ [] ++
    (rounds.flatMap PartitionRoundWitness.corrEdges).map IndexedEdge.toWeighted)
  have hmsf_d := partition_isMinSpanningForest (F_comps := F_comps) (H_lift := []) (F := F)
    (hperm_r.map IndexedEdge.toWeighted) hcov_r hrel_conglom
    (fun i => by
      fin_cases i
      · refine ⟨htr0_sub, fun x hx hxprev => ?_⟩
        simp at hxprev
      · refine ⟨htr1_sub, fun x hx hxprev => ?_⟩
        have hx0 : x ∈ r0.verts := by
          simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and] at hxprev
          obtain ⟨j, hj, hzj⟩ := hxprev
          dsimp only [rounds] at j hj hzj
          rcases j with ⟨j, hj2⟩
          match j with
          | 0 => exact hzj
          | 1 => simp at hj
        exact hprev1 x hx (by rwa [hdeadSet1]))
    (fun i e he => by
      obtain ⟨eIdx, he_f, rfl⟩ := List.mem_map.mp he
      have hf := (List.mem_filter.mp he_f).2
      simp only [decide_eq_true_eq] at hf
      let eL : Fin L.es.length := ⟨eIdx.val, hm_esK3 ▸ eIdx.isLt⟩
      have heL_eq : L.es[eL.val]'eL.isLt = esK3[eIdx.val]'eIdx.isLt :=
        hcast_es eIdx.val eL.isLt eIdx.isLt
      have heIdxL : eL ∉ em0 := fun hm =>
        hf.1 (List.mem_map.mpr ⟨_, hm, by ext; rfl⟩)
      have heIdxL1 : eL ∉ em1 := fun hm =>
        hf.2 (List.mem_map.mpr ⟨_, hm, by ext; rfl⟩)
      have hcr0' : eL ∉ corr0 := by simp [hcorr0_nil]
      have hcr1' : eL ∉ corr1 := by simp [hcorr1_nil]
      fin_cases i
      · dsimp only [rounds]
        rw [← heL_eq]
        exact ⟨fun ⟨hu, hv⟩ => heIdxL ((hemit0_iff eL).mpr ⟨rfl, hu, hv⟩),
          fun s_st hcr => huncorr0 eL rfl heIdxL hcr0' s_st hcr⟩
      · have hes1 : s2.mem (L.bufBase + 14 * 3 + eIdx.val) = 0 := by
          rw [hest0_fn' eIdx.val eL.isLt]
          have hnot0 : ¬∃ hlt, (⟨eIdx.val, hlt⟩ : Fin L.es.length) ∈ em0 := fun ⟨_, hm⟩ => heIdxL hm
          have hnot1 : ¬∃ hlt, (⟨eIdx.val, hlt⟩ : Fin L.es.length) ∈ corr0 :=
            fun ⟨_, hm⟩ => hcr0' hm
          simp [hnot0, hnot1]
        dsimp only [rounds]
        rw [← heL_eq]
        exact ⟨fun ⟨hu, hv⟩ => heIdxL1 ((hemit1_iff eL).mpr ⟨hes1, hu, hv⟩),
          fun s_st hcr => huncorr1 eL hes1 heIdxL1 hcr1' s_st hcr⟩)
    (fun i j hij e he => by
      have hi_lt : i.val < 2 := by simpa [heq_rounds] using i.isLt
      have hj_lt : j.val < 2 := by simpa [heq_rounds] using j.isLt
      have hi0 : i.val = 0 := by omega
      have hj1 : j.val = 1 := by omega
      have hi_eq : i = ⟨0, by simp [heq_rounds]⟩ := Fin.ext hi0
      have hj_eq : j = ⟨1, by simp [heq_rounds]⟩ := Fin.ext hj1
      subst hi_eq hj_eq
      have htr1_w' : treeIdx1.map IndexedEdge.toWeighted = r1.tree.treeEdges := by
        simpa [rounds] using htr1_w
      have he' : e ∈ r1.tree.treeEdges := by simpa [rounds] using he
      rw [← htr1_w', List.mem_map] at he'
      obtain ⟨ei, hei, rfl⟩ := he'
      obtain ⟨eIdx, rfl, hes1⟩ := htr1_src ei hei
      have heIdx_not_em0 : eIdx ∉ em0 := fun hm => by
        rw [hest0_fn' eIdx.val eIdx.isLt] at hes1
        simp [hm] at hes1
      have hcr0' : eIdx ∉ corr0 := by simp [hcorr0_nil]
      dsimp only [rounds]
      exact fun s_st hcr => huncorr0 eIdx rfl heIdx_not_em0 hcr0' s_st hcr)
    (by simp [F_comps, heq_rounds])
    (fun i => by fin_cases i <;> exact kruskalEdges_isMinSpanningForest _)
    List.nil_subperm (by simpa [contractEdgeList] using isMinSpanningForest_fin1_loops)
    (kruskalEdges_isMinSpanningForest _)
  -- Also test partitionProg_spec on K_3 with maxsize = 2
  have hspec := partitionProg_spec (by decide) hinit.1 (maxsize := 2) (by decide) hinit.2.2
    (by rw [hinit.2.1]; decide) (by rw [hinit.2.1]; decide) isSimple_esK3
  rcases hspec with ⟨hsafe_p, _, _, _, _, _, _, hnc_le, hmc_le, _, _, _, _, _, _, _, _,
    p_rounds, _, _, hrl_p, _, _, _, _, _, _, _, _, _, hcov_p, hmeta_p, hround_p, _, _, _, _⟩
  have hmc0_p : rProg.1.mcLen = 0 :=
    Nat.eq_zero_of_le_zero (by simpa [rProg, execWordRAM, s0, esK3] using hmc_le)
  have h2_le_p : 2 ≤ rProg.1.numComps := by
    have hcov_card : (Finset.univ : Finset (Fin 3)).card ≤
        ∑ i : Fin p_rounds.length, (p_rounds[i.val]'i.isLt).verts.card := by
      calc (Finset.univ : Finset (Fin 3)).card
          ≤ (Finset.univ.biUnion fun i : Fin p_rounds.length =>
              (p_rounds[i.val]'i.isLt).verts).card := Finset.card_le_card fun x _ => by
                obtain ⟨q, hq, hxq⟩ := hcov_p x
                obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hq
                exact Finset.mem_biUnion.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, hxq⟩
        _ ≤ ∑ i : Fin p_rounds.length, (p_rounds[i.val]'i.isLt).verts.card :=
            Finset.card_biUnion_le
    have hsum_le : (∑ i : Fin p_rounds.length, (p_rounds[i.val]'i.isLt).verts.card) ≤
        2 * p_rounds.length := by
      calc (∑ i : Fin p_rounds.length, (p_rounds[i.val]'i.isLt).verts.card)
          ≤ ∑ _i : Fin p_rounds.length, 2 := Finset.sum_le_sum fun i _ => by
            have hvc := (hround_p i).2.2.2.1
            have hnv_m := hmeta_p.numVerts_le i
            omega
        _ = 2 * p_rounds.length := by simp [Finset.sum_const, Nat.mul_comm]
    rw [Finset.card_fin] at hcov_card
    have : 2 ≤ p_rounds.length := by omega
    simpa [rProg, execWordRAM, s0, esK3, hrl_p] using this
  rw [hL_max] at hact_d
  exact ⟨⟨r0, r1, H_rem, conglomFn, F, hr0_card_eq2, hr1_card_eq2, hinter1_ne, hstop_some1,
    hperm_r, hrel_conglom, hopt_d, hact_d, hmsf_d⟩, by simpa [s0, esK3] using hsafe_p, h2_le_p,
    by simpa [rProg, execWordRAM, s0, esK3] using hnc_le, hmc0_p⟩

/-! ## 5. Multigraph Boundaries: Parallel Edges & `m > n` -/

private def esPar : List (IndexedEdge 3) :=
  [⟨⟨0, by decide⟩, ⟨1, by decide⟩, 7, 0⟩,
   ⟨⟨0, by decide⟩, ⟨1, by decide⟩, 2, 1⟩,
   ⟨⟨1, by decide⟩, ⟨2, by decide⟩, 4, 2⟩]

-- Test (e1): Parallel-edge loopless multigraph via `partSetup_spec` + `partRoundInit_spec` +
-- `partDjpLoop_spec` + `partRoundFinish_spec`: visits all 3 vertices (`D.numSteps = 2`),
-- emits all 3 multigraph edges (including both parallel `(0, 1)` edges), zero corrupted edges.
example :
    let s0 := mkInitState esPar
    let setup := (Memory.spec 0).clientResult s0 (partSetup ⟨3, 3, 0, 3⟩)
    let s1 := (Memory.spec 0).clientState s0 (partSetup ⟨3, 3, 0, 3⟩)
    let st0 : PartOuterState := ⟨0, 0, 0, 0, 0, 0, setup.sh⟩
    let prog := partRunRound (setup.env, st0)
    let rRound := execWordRAM s1 prog
    (Memory.spec 16).ValidHistory s1 ((Memory.spec 16).clientHistory s1 prog) ∧
    rRound.1.numComps = 1 ∧ rRound.1.cEdgeLen = 3 ∧ rRound.1.mcLen = 0 ∧ rRound.1.tLen = 2 := by
  intro s0 setup s1 st0 prog rRound
  have hinit := mkInitState_spec (w := 16) esPar (by decide) (by decide)
    (fun e he => by simp only [esPar, List.mem_cons, List.not_mem_nil, or_false] at he
                    rcases he with rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩)
  have hsetup := partSetup_spec (w := 16) (n := 3) (edgeBase := 0) (maxsize := 3) (by decide)
    hinit.1 (by decide) (by decide) hinit.2.2 (by rw [hinit.2.1]; decide)
    (by rw [hinit.2.1]; decide)
  rcases hsetup with ⟨_, _, _, _, hm, _, hmax, _, hsh_eq, hs1_fr, _, _, hin1, hcsr1,
    hsh1, hbuf1, hedge1, L, hL_env, hL_es, hL_eb, hL_max, hL_off, hL_adj, hL_it, hL_nd, hL_bf, _⟩
  have hm3 : L.es.length = 3 := by rw [hL_es]; rfl
  have hs1_fr' : s1.frontier = L.bufBase + (14 * 3 + 14 * L.es.length) := by
    simpa [s1, s0, esPar, hL_bf, hm3] using hs1_fr
  have hsh_eq' : setup.sh =
      ⟨setup.sh.itemBase, setup.sh.nodeBase, 0, 0, 0, partRankThreshold⟩ := by
    simpa [setup, s0, esPar] using hsh_eq
  have hib_eq' : setup.sh.itemBase = L.itemBase := by
    simpa [setup, s0, esPar] using hL_it.symm
  have hnb_eq' : setup.sh.nodeBase = L.nodeBase := by
    simpa [setup, s0, esPar] using hL_nd.symm
  have hsh1' : SHInv 16 0 0 (2 * L.es.length) (4 * L.es.length) setup.sh [] (fun _ => 0) s1 := by
    have hsh1_0 := hsh1
    rw [hsh_eq] at hsh1_0
    have hsh_raw : setup.sh =
        ⟨setup.sh.itemBase, setup.sh.nodeBase, 0, 0, 0, partRankThreshold⟩ := hsh_eq'
    rw [hsh_raw, hm3]
    simpa [setup, s1, s0, esPar] using hsh1_0
  have hcsr1' : HoldsUndirCSR L.offBase L.adjBase L.es s1.mem := by
    simpa [s1, s0, esPar, hL_off, hL_adj, hL_es] using hcsr1
  have hin1' : HoldsIndexedEdges L.edgeBase L.es s1.mem := by
    simpa [s1, s0, esPar, hL_eb, hL_es] using hin1
  have hbuf1' : ∀ j < 6, s1.mem (L.bufBase + j) = 0 := by
    simpa [s1, s0, esPar, hL_bf] using hbuf1
  have hedge1' : ∀ j < L.es.length, s1.mem (L.bufBase + 14 * 3 + j) = 0 := by
    simpa [s1, s0, esPar, hL_bf, hm3] using hedge1
  have hloopless : ∀ e : Fin L.es.length, (L.es[e.val]'e.isLt).u ≠ (L.es[e.val]'e.isLt).v := by
    intro e
    have he : e.val < 3 := Nat.lt_of_lt_of_eq e.isLt hm3
    rcases (show e.val = 0 ∨ e.val = 1 ∨ e.val = 2 by omega) with h | h | h <;>
      simp [hL_es, esPar, h]
  have hrem0 : remDeg 3 L.offBase s1.mem (Finset.univ.filter fun x : Fin 3 => (0 : ℕ) ≠ 0) = 6 := by
    simpa [hm3] using remDeg_empty hcsr1'
  have hic0 : setup.sh.itemCount = 0 := by rw [hsh_eq']
  have hinit_r := partRoundInit_spec L (fun _ => 0) (fun _ => 0) (fun _ => 0) 1 0 0 0
    ⟨0, by decide⟩ setup.sh s1 hs1_fr' hib_eq' hnb_eq'
    (by rw [hsh_eq']) hic0 hsh1' hcsr1' hin1'
    (fun x hx => by rw [Nat.add_assoc]; exact hbuf1' (3 + x) (by omega))
    (fun x hx => by have hz := hbuf1' (3 + x) (by omega); omega)
    (by decide) rfl hedge1' hloopless (by simp) (by rw [hrem0, hm3])
  rcases hinit_r with ⟨_, hvh_in, _, _, W0, _⟩
  let h1 := (Memory.spec 0).clientResult s1 (partRoundInit ⟨L.toEnv, 1, 0, setup.sh⟩)
  let s2 := (Memory.spec 0).clientState s1 (partRoundInit ⟨L.toEnv, 1, 0, setup.sh⟩)
  have hloop := partDjpLoop_spec L s1 (fun _ => 0) (fun _ => 0) (fun _ => 0) 1 0 0 0
    ⟨0, by decide⟩ hcsr1' hin1'
    (fun x hx => hbuf1' x (by omega)) hedge1'
    (fun x hx => by have hz := hbuf1' (3 + x) (by omega); omega)
    (by decide) hloopless h1 s2 W0
  rcases hloop with ⟨_, hvh_lp, ha_cont, _, _, W1, _⟩
  let st_lp := (Memory.spec 0).clientResult s2 (partDjpLoop ⟨L.toEnv, 1, 0, h1⟩)
  let s3 := (Memory.spec 0).clientState s2 (partDjpLoop ⟨L.toEnv, 1, 0, h1⟩)
  have hst_eta : st_lp = ⟨0, st_lp.hitPrev, st_lp.size, st_lp.tLen, st_lp.sh⟩ := by
    conv_lhs => change PartDjpState.mk st_lp.cont st_lp.hitPrev st_lp.size st_lp.tLen st_lp.sh
    rw [ha_cont]
  have W1' : DjpWitness L s1 (fun _ => 0) (fun _ => 0) (fun _ => 0) 1 0 0 0 ⟨0, by decide⟩
      ⟨0, st_lp.hitPrev, st_lp.size, st_lp.tLen, st_lp.sh⟩ s3 := by
    rw [← hst_eta]; dsimp only [st_lp, s3]; exact W1
  have hfin := partRoundFinish_spec L s1 (fun _ => 0) (fun _ => 0) (fun _ => 0) 0 0 0
    ⟨0, by decide⟩ 0 0 0 0 0 setup.sh st_lp.sh st_lp.hitPrev st_lp.size st_lp.tLen s3 W1'
    hcsr1' hin1' (fun x hx => hbuf1' x (by omega)) hedge1'
    (fun x hx => by have hz := hbuf1' (3 + x) (by omega); omega)
    hloopless (by decide) (by decide)
    (by have hsz_le := W1'.hsize_le; rw [hL_max] at hsz_le; dsimp only at hsz_le; omega)
    (by simp)
  rcases hfin with ⟨_, hvh_fn, hu_fn, hnc_fn, _, _, _, htl_fn, _, _, _, _, _, _, _, hmc_diff,
    _, _, _, _, _, _, _, emIdx, corrIdx, compLocal, hnd_em, _, _, hcp_len, hcr_len,
    _, hmap_cp, _, hemit_iff, _, _, _, hno_cross, _, _⟩
  have hno_hit : st_lp.hitPrev = 0 := by
    by_contra hne
    have hp1 := W1'.hhit_prev hne
    exact absurd rfl (hp1.2.2.2 hp1.2.2.1)
  have hr_root : W1'.D.root = ⟨0, by decide⟩ := W1'.hroot
  have hsz_eq : st_lp.size = W1'.D.numSteps + 1 := W1'.hsize
  have hsz_le : st_lp.size ≤ 3 := by simpa [hL_max] using W1'.hsize_le
  have hV_univ : W1'.D.treeVerts W1'.D.numSteps = Finset.univ := by
    have h0 : (⟨0, by decide⟩ : Fin 3) ∈ W1'.D.treeVerts W1'.D.numSteps :=
      Eq.mp (congrArg (· ∈ W1'.D.treeVerts W1'.D.numSteps) hr_root)
        (mem_djpVerts_mono _ _ (Nat.zero_le _) (by simp [djpVerts]))
    have hlt_false : st_lp.size < L.maxsize → False := fun hlt => by
      have hnc_e := hno_cross hno_hit hlt
      have h1_in : (⟨1, by decide⟩ : Fin 3) ∈ W1'.D.treeVerts W1'.D.numSteps := by
        have hc := hnc_e ⟨0, hm3.symm ▸ (by decide : 0 < 3)⟩ rfl
        simp only [hL_es, esPar, List.getElem_cons_zero] at hc
        by_contra hnot; exact hc ⟨fun _ => hnot, fun _ => h0⟩
      have h2_in : (⟨2, by decide⟩ : Fin 3) ∈ W1'.D.treeVerts W1'.D.numSteps := by
        have hc := hnc_e ⟨2, hm3.symm ▸ (by decide : 2 < 3)⟩ rfl
        simp only [hL_es, esPar, List.getElem_cons_succ, List.getElem_cons_zero] at hc
        by_contra hnot; exact hc ⟨fun _ => hnot, fun _ => h1_in⟩
      have hu : W1'.D.treeVerts W1'.D.numSteps = Finset.univ := by
        ext x; refine ⟨fun _ => Finset.mem_univ _, fun _ => ?_⟩
        fin_cases x <;> assumption
      have hdc := djpVerts_card W1'.D W1'.D.numSteps le_rfl
      rw [hu, Finset.card_fin, ← hsz_eq] at hdc; omega
    have hsz3 : st_lp.size = 3 := by
      have h1 : st_lp.size ≤ L.maxsize := hL_max.symm ▸ hsz_le
      by_contra hne; exact hlt_false (by omega)
    have hdc := djpVerts_card W1'.D W1'.D.numSteps le_rfl
    have hcard3 : (W1'.D.treeVerts W1'.D.numSteps).card = 3 := by omega
    exact Finset.eq_univ_of_card _ (by simpa [Fintype.card_fin] using hcard3)
  have hsteps2 : W1'.D.numSteps = 2 := by
    have hdc := djpVerts_card W1'.D W1'.D.numSteps le_rfl
    rw [hV_univ, Finset.card_fin] at hdc; omega
  have htlen2 : st_lp.tLen = 2 := by
    have ht : st_lp.tLen = 0 + W1'.D.numSteps := W1'.htlen
    rw [ht, Nat.zero_add, hsteps2]
  have hem_perm : emIdx.Perm (List.finRange L.es.length) :=
    (List.perm_ext_iff_of_nodup hnd_em (List.nodup_finRange _)).mpr fun i =>
      ⟨fun _ => List.mem_finRange i, fun _ => (hemit_iff i).mpr
        ⟨rfl, hV_univ ▸ Finset.mem_univ _, hV_univ ▸ Finset.mem_univ _⟩⟩
  have hnc_setup : setup.sh.nodeCount = 0 := by rw [hsh_eq']
  have hfn_res :
      (Memory.spec 0).clientResult s3
          (partRoundFinish ⟨L.toEnv, st0, setup.sh.nodeCount, st_lp⟩) =
      (Memory.spec 0).clientResult s3 (partRoundFinish
        ⟨L.toEnv, st0, 0, ⟨0, st_lp.hitPrev, st_lp.size, st_lp.tLen, st_lp.sh⟩⟩) := by
    rw [hnc_setup]
    exact congrArg (fun d' =>
      (Memory.spec 0).clientResult s3 (partRoundFinish ⟨L.toEnv, st0, 0, d'⟩)) hst_eta
  have hce_eq : ((Memory.spec 0).clientResult s3 (partRoundFinish
      ⟨L.toEnv, st0, setup.sh.nodeCount, st_lp⟩)).cEdgeLen = 3 := by
    have hce_fin : ((Memory.spec 0).clientResult s3 (partRoundFinish
        ⟨L.toEnv, st0, setup.sh.nodeCount, st_lp⟩)).cEdgeLen = compLocal.length := by
      rw [hfn_res]; simpa using hcp_len.symm
    have h1 : compLocal.length = emIdx.length := by
      have h2 := congrArg List.length hmap_cp; simpa using h2
    rw [hce_fin, h1, hem_perm.length_eq, List.length_finRange, hm3]
  have hmc_eq : ((Memory.spec 0).clientResult s3 (partRoundFinish
      ⟨L.toEnv, st0, setup.sh.nodeCount, st_lp⟩)).mcLen = 0 := by
    have hic_le : st_lp.sh.itemCount ≤ 6 := by simpa [hm3] using W1'.hic_le
    have hdiff : 16 * ((Memory.spec 0).clientResult s3 (partRoundFinish
        ⟨L.toEnv, st0, setup.sh.nodeCount, st_lp⟩)).mcLen ≤ st_lp.sh.itemCount := by
      rw [hfn_res]; simpa using hmc_diff
    omega
  have hL_env' : L.toEnv = setup.env := by simpa [setup, s0, esPar] using hL_env
  have hprog_rr : prog =
      (partRoundInit ⟨L.toEnv, 1, 0, setup.sh⟩ >>= fun h1' =>
        partDjpLoop ⟨L.toEnv, 1, 0, h1'⟩ >>= fun st1' =>
          partRoundFinish ⟨L.toEnv, st0, setup.sh.nodeCount, st1'⟩) := by
    dsimp only [prog]
    rw [← hL_env', partRunRound_def]
  have hvh_fn' : (Memory.spec 16).ValidHistory s3
      ((Memory.spec 16).clientHistory s3 (partRoundFinish ⟨L.toEnv, st0, 0, st_lp⟩)) := by
    rw [hst_eta]; exact hvh_fn
  have hvh_all : (Memory.spec 16).ValidHistory s1 ((Memory.spec 16).clientHistory s1 prog) := by
    rw [hprog_rr]
    refine validHistory_bind_step hvh_in ?_
    refine validHistory_bind_step hvh_lp ?_
    rw [hnc_setup]
    exact hvh_fn'
  have hres_eq : (Memory.spec 0).clientResult s1 prog =
      (Memory.spec 0).clientResult s3 (partRoundFinish
        ⟨L.toEnv, st0, setup.sh.nodeCount, st_lp⟩) := by
    rw [hprog_rr, StateTransitionSpec.clientResult_bind,
      StateTransitionSpec.clientResult_bind]
  refine ⟨hvh_all, ?_, ?_, ?_, ?_⟩
  · dsimp only [rRound, execWordRAM]; rw [hres_eq, hfn_res]; simpa using hnc_fn
  · dsimp only [rRound, execWordRAM]; rw [hres_eq]; exact hce_eq
  · dsimp only [rRound, execWordRAM]; rw [hres_eq]; exact hmc_eq
  · dsimp only [rRound, execWordRAM]; rw [hres_eq, hfn_res, htl_fn, htlen2]

private def esK4m1 : List (IndexedEdge 4) :=
  [⟨⟨0, by decide⟩, ⟨1, by decide⟩, 2, 0⟩,
   ⟨⟨1, by decide⟩, ⟨2, by decide⟩, 3, 1⟩,
   ⟨⟨2, by decide⟩, ⟨3, by decide⟩, 4, 2⟩,
   ⟨⟨0, by decide⟩, ⟨2, by decide⟩, 5, 3⟩,
   ⟨⟨1, by decide⟩, ⟨3, by decide⟩, 6, 4⟩]

private theorem isSimple_esK4m1 : IsSimple (edgeEnds (esK4m1.map IndexedEdge.toWeighted)) := by
  refine isSimple_of_pairs (fun i => by fin_cases i <;> decide) fun i j hij => ?_
  fin_cases i <;> fin_cases j <;> simp_all [esK4m1]

-- Test (e2): Simple `m > n` multigraph (`K_4 \ e`, `n = 4, m = 5, maxsize = 4`).
example :
    let s0 := mkInitState esK4m1
    let d : PartSetupArgs := ⟨4, 5, 0, 4⟩
    let r := execWordRAM s0 (partitionProg d)
    partitionProgSafe 16 d s0 ∧
    (Memory.spec 16).ValidHistory s0 ((Memory.spec 16).clientHistory s0 (partitionProg d)) ∧
    Memory.WellFormed 16 r.2.1 ∧ r.2.2 ≤ 6000 * 9 ∧
    1 ≤ r.1.numComps ∧ r.1.numComps ≤ 4 ∧ r.1.mcLen = 0 ∧
    (∃ (rounds : List (PartitionRoundWitness 4)),
      (rounds.map fun q => optDepth (edgeEnds (q.compLocal.map IndexedEdge.toWeighted))).sum ≤
        optDepthMN 5 4) := by
  intro s0 d r
  have hinit := mkInitState_spec (w := 16) esK4m1 (by decide) (by decide)
    (fun e he => by simp only [esK4m1, List.mem_cons, List.not_mem_nil, or_false] at he
                    rcases he with rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩)
  have hspec := partitionProg_spec (by decide) hinit.1 (maxsize := 4) (by decide) hinit.2.2
    (by rw [hinit.2.1]; decide) (by rw [hinit.2.1]; decide) isSimple_esK4m1
  rcases hspec with ⟨hsafe, hvh, hwf', _, _, _, hcost, hnc_le, hmc_le, _, _, _, _, _, _, _, _,
    rounds, _, _, hrl, _, _, hperm, _, _, _, _, _, _, hcov, hmeta, _, _, _, _, _⟩
  have hmc0 : r.1.mcLen = 0 :=
    Nat.eq_zero_of_le_zero (by simpa [r, execWordRAM, s0, d, esK4m1] using hmc_le)
  have h1_le : 1 ≤ r.1.numComps := by
    obtain ⟨q, hq, _⟩ := hcov ⟨0, by decide⟩
    exact Nat.succ_le_of_lt (by
      simpa [r, execWordRAM, s0, d, esK4m1, hrl] using List.length_pos_of_mem hq)
  have hopt := partition_optDepth_sum_le isSimple_esK4m1 (subperm_compGlobal_of_perm hperm)
    fun i => ⟨hmeta.lift_injective i, hmeta.compGlobal_verts i,
      hmeta.inter_prev_card_le_one i⟩
  exact ⟨by simpa [s0, d, esK4m1] using hsafe, by simpa [s0, d, esK4m1] using hvh,
    by simpa [r, execWordRAM, s0, d, esK4m1] using hwf',
    by simpa [r, execWordRAM, s0, d, esK4m1] using hcost,
    h1_le, by simpa [r, execWordRAM, s0, d, esK4m1] using hnc_le, hmc0, rounds, hopt⟩

/-! ## 6. Deterministic Width-Blind `Program .standard` Lowering -/

-- Test (f): Lowered deterministic width-blind `Program .standard` execution of `partitionProg`
-- on `K_2` (`words = [2, 1, 5, 2, 0, 1, 5, 0]`) returning `numComps ∈ {1, 2}` at `.halt`.
example :
    let words : List ℕ := [2, 1, 5, 2, 0, 1, 5, 0]
    ∃ r C pc : ℕ, ∃ prog : Program .standard r, ¬prog.ReadsWidth ∧ prog.IsRandFree ∧
      ∃ frontier : Fin r, ∃ y, ∃ n nr : ℕ,
        Runs 16 prog (State.init words) ⟨pc, y⟩ n ∧
        step 16 prog ⟨pc, y⟩ = .halt nr ∧
        1 ≤ nr ∧ nr ≤ 2 ∧
        (memoryState frontier y).frontier ≤ 297 ∧
        n + 1 ≤ C * (6000 * 3 + 1) + 1 := by
  intro words
  obtain ⟨r, C, pc, prog, hnw, frontier, _, hrun⟩ :=
    realizes_partitionProg.exists_standard_basis_init_program_state_from_words (0 : Fin 9)
  have hprog_rf : (stripRand prog).IsRandFree := isRandFree_stripRand prog
  have hprog_nw : ¬(stripRand prog).ReadsWidth := not_readsWidth_stripRand hnw
  let d : PartSetupArgs := ⟨2, 1, 5, 2⟩
  let es : List (IndexedEdge 2) := [⟨⟨0, by decide⟩, ⟨1, by decide⟩, 5, 0⟩]
  have hlayout : ∀ j : Fin 4, words.getD j.val 0 = WordEncoding.encode d j := by
    intro j; fin_cases j <;> rfl
  have hwf : Memory.WellFormed 16 (Memory.State.init words) :=
    Memory.wellFormed_init (by dsimp only [words]; decide) (by dsimp only [words]; decide)
  have hin : HoldsIndexedEdges 5 es (Memory.State.init words).mem := fun i hi => by
    have hi0 : i = 0 := by simp [es] at hi; omega
    subst hi0
    dsimp only [es, words]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl
  have hsimp : IsSimple (edgeEnds (es.map IndexedEdge.toWeighted)) :=
    isSimple_of_pairs (fun i => by fin_cases i; decide)
      (fun i j hij => by fin_cases i; fin_cases j; omega)
  have hspec := partitionProg_spec (by decide) hwf (maxsize := 2) (by decide) hin
    (by dsimp only [es, words, Memory.State.init]; decide)
    (by dsimp only [es, words, Memory.State.init]; decide) hsimp
  rcases hspec with ⟨hsafe, hvh, _, _, _, hfr_ub, hcost, hnc_le, _, _, _, _, _, _, _, _, _,
    rounds, _, _, hrl, _, _, _, _, _, _, _, _, _, hcov, _⟩
  have hvh16 : (Memory.spec 16).ValidHistory (Memory.State.init words)
      ((Memory.spec 16).clientHistory (Memory.State.init words) (partitionProg d)) := by
    simpa [es] using hvh
  obtain ⟨y, n, hruns, hhalt, hmem_eq, _, hsteps⟩ :=
    hrun 16 d words hlayout (by dsimp only [words]; decide)
      (by dsimp only [words]; decide) (by dsimp only [words]; decide) hsafe hvh16
  let res0 := (Memory.spec 0).clientResult (Memory.State.init words) (partitionProg d)
  have hres_eq : WordEncoding.encode
      ((Memory.spec 16).clientResult (Memory.State.init words) (partitionProg d)) (0 : Fin 9) =
      res0.numComps := by
    rw [clientResult_width 16]; rfl
  have hst_eq :
      ((Memory.spec 16).clientState (Memory.State.init words) (partitionProg d)).frontier =
      ((Memory.spec 0).clientState (Memory.State.init words) (partitionProg d)).frontier := by
    rw [clientState_width 16]
  have hhalt' : step 16 prog ⟨pc, y⟩ = .halt res0.numComps := by
    rw [hres_eq] at hhalt; exact hhalt
  have hfr' : (memoryState frontier y).frontier ≤ 297 := by
    rw [hmem_eq, hst_eq]
    exact hfr_ub.trans (by dsimp only [words, Memory.State.init, es]; decide)
  have h1_le : 1 ≤ res0.numComps := by
    obtain ⟨q, hq, _⟩ := hcov ⟨0, by decide⟩
    exact Nat.succ_le_of_lt (by simpa [res0, d, es, hrl] using List.length_pos_of_mem hq)
  have hnc_le' : res0.numComps ≤ 2 := by simpa [res0, d, es] using hnc_le
  have hsteps' : n + 1 ≤ C * (6000 * 3 + 1) + 1 := by
    rw [Nat.add_zero] at hsteps
    have hcost' : memoryCost (partitionProg d) (Memory.State.init words) ≤ 6000 * 3 := by
      simpa [es] using hcost
    exact hsteps.trans (Nat.add_le_add_right
      (Nat.mul_le_mul_left C (Nat.add_le_add_right hcost' 1)) 1)
  exact ⟨r, C, pc, stripRand prog, hprog_nw, hprog_rf, frontier, y, n, res0.numComps,
    runs_stripRand hruns, step_stripRand_of_halt hhalt', h1_le, hnc_le', hfr', hsteps'⟩

end CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.PartitionOuter
