/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: local-only (tests for OptimalMSF driver and Theorem 5.8)

import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.Contraction.Threshold
import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.OptimalMSF.Driver
import CslibFrontier.Computability.WordRAM.Realization.Program.Standard
import CslibFrontier.Tactic.Fits

/-!
# Tests for Optimal MSF Driver and Theorem 5.8

Exercises `OptimalMSF/Driver.lean` across:

1. Empty (`m = 0`) and single-edge (`m = 1`) concrete graph witnesses via `optimalMSFProg_spec`.
2. A nontrivial multigraph (`m = 7`, `n = 5`) containing a self-loop, parallel heavier edge,
   cycle chord, and isolated vertex via both `optimalMSFProg_spec` and `optimalMSF_wordRAM_spec`.
3. Connected `SimpleGraph (Fin 4)` instantiation of `optimalMSF_simpleGraph_isMST_spec` and
   `isMST_toSimpleGraph_of_isMinSpanningForest`, verifying Mathlib `SimpleGraph.IsMST`.
4. Direct width-blind `Program .standard` lowering from `realizes_optimalMSFProg` via
   `exists_standard_basis_init_program_state_from_words` and `stripRand`.
-/

-- This test module intentionally exports no declarations.
set_option linter.privateModule false

namespace CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.OptimalMSFDriver

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.Algorithms.Lean.Kruskal Cslib.Algorithms.WordRAM.Kruskal
open Cslib.Query.MinimumSpanningForest
open Cslib.Algorithms.WordRAM.MinimumSpanningForest

/-! ## 1. Empty (`m = 0`) and single-edge (`m = 1`) witnesses -/

private theorem fits24_of_le {x : ℕ} (hx : x ≤ 1000000) : Fits 24 x :=
  (by decide : Fits 24 1000000).of_le hx

private theorem fits24_wordBound {n m : ℕ} (hn : n ≤ 5) (hm : m ≤ 10) :
    Fits 24 (optimalMSFWordBound n m) := by
  unfold optimalMSFWordBound
  have hlog : Nat.iterLog 3 n ≤ n := Nat.iterLog_le_self 3 n
  have h1 : m * max 1 (Nat.iterLog 3 n) ≤ 10 * 5 := Nat.mul_le_mul hm (by omega)
  have hmul : 2 * m * max 1 (Nat.iterLog 3 n) ≤ 2 * 10 * 5 := by
    rw [Nat.mul_assoc]; omega
  exact fits24_of_le (by omega)

private theorem emptyGraph_msf_witness :
    let es : List (WeightedEdge 4 ℕ) := []
    let s := Memory.State.init (encode es)
    let prog := optimalMSFProg ⟨4, 0⟩
    optimalMSFSafe 24 ⟨4, 0⟩ s ∧
    (Memory.spec 24).ValidHistory s ((Memory.spec 24).clientHistory s prog) ∧
    IsMinSpanningForest es [] ∧
    outputList ((Memory.spec 0).clientState s prog).mem
        ((Memory.spec 0).clientResult s prog) =
      encodeEdges ([] : List (WeightedEdge 4 ℕ)) := by
  have hfit : Fits 24 (optimalMSFWordBound 4 ([] : List (WeightedEdge 4 ℕ)).length) :=
    fits24_wordBound (by omega) (by decide)
  have hspec := optimalMSFProg_spec (w := 24) (n := 4) [] (fun _ h => by simp at h) hfit
  have hlen0 : ([] : List (WeightedEdge 4 ℕ)).length = 0 := rfl
  rw [hlen0] at hspec
  obtain ⟨hsafe, hv, msfEs, hmsf, hlen, hout, _, _⟩ := hspec
  have hnil : msfEs = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hlen)
  subst hnil
  exact ⟨hsafe, hv, hmsf, hout⟩

private def oneEdgeRawEs : List (WeightedEdge 3 ℕ) :=
  [⟨0, 2, 7⟩]

private theorem oneEdge_msf_witness :
    let s := Memory.State.init (encode oneEdgeRawEs)
    let prog := optimalMSFProg ⟨3, 1⟩
    let outBase := (Memory.spec 0).clientResult s prog
    let s' := (Memory.spec 0).clientState s prog
    optimalMSFSafe 24 ⟨3, 1⟩ s ∧
    (Memory.spec 24).ValidHistory s ((Memory.spec 24).clientHistory s prog) ∧
    IsMinSpanningForest oneEdgeRawEs oneEdgeRawEs ∧
    outputList s'.mem outBase = [0, 2, 7] ∧
    Fits 24 (outBase + 3) ∧
    memoryCost prog s ≤ 30 * optDepthMN 1 3 + 78800 * 1 + 651500 * 3 + 1814300 := by
  have hfit : Fits 24 (optimalMSFWordBound 3 oneEdgeRawEs.length) :=
    fits24_wordBound (by omega) (by decide)
  have hspec := optimalMSFProg_spec (w := 24) (n := 3) oneEdgeRawEs
    (fun e he => by
      simp only [oneEdgeRawEs, List.mem_singleton] at he
      rw [he]; exact fits24_of_le (by decide))
    hfit
  have hlen1 : oneEdgeRawEs.length = 1 := rfl
  rw [hlen1] at hspec
  obtain ⟨hsafe, hv, msfEs, hmsf, hlen, hout, hfit_out, hcost⟩ := hspec
  have hmsf_eq : msfEs = oneEdgeRawEs := by
    have hnon : msfEs ≠ [] := by
      intro hem
      have hpart := hmsf.1.2.2
      rw [hem] at hpart
      have hc0 : (edgePartition oneEdgeRawEs).numComponents = 2 := by decide
      have hc1 : (edgePartition ([] : List (WeightedEdge 3 ℕ))).numComponents = 3 := by decide
      rw [← hpart] at hc0
      omega
    rcases msfEs with _ | ⟨e, rest⟩
    · exact absurd rfl hnon
    · rw [List.length_cons] at hlen
      have hrest : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hrest
      have hmem := hmsf.1.1.subset List.mem_cons_self
      simp only [oneEdgeRawEs, List.mem_singleton] at hmem
      subst hmem
      rfl
  rw [hmsf_eq] at hmsf hout hfit_out
  rw [hlen1, Nat.mul_one] at hfit_out
  exact ⟨hsafe, hv, hmsf, hout.trans (by rfl), hfit_out, hcost⟩

/-! ## 2. Nontrivial multigraph witnesses (`optimalMSFProg_spec`, `optimalMSF_wordRAM_spec`) -/

private def multiRawEs : List (WeightedEdge 5 ℕ) :=
  [ ⟨1, 1, 1⟩,
    ⟨0, 1, 9⟩,
    ⟨1, 0, 3⟩,
    ⟨1, 2, 3⟩,
    ⟨2, 3, 3⟩,
    ⟨0, 2, 8⟩,
    ⟨3, 0, 6⟩ ]

private def multiRawRef : List (WeightedEdge 5 ℕ) :=
  [⟨1, 0, 3⟩, ⟨1, 2, 3⟩, ⟨2, 3, 3⟩]

private theorem multiRawRef_isMSF : IsMinSpanningForest multiRawEs multiRawRef := by
  have hsub : multiRawRef.Subperm multiRawEs :=
    (List.Sublist.cons _ (.cons _ (.cons_cons _ (.cons_cons _ (.cons_cons _
      (.cons _ (.cons _ .slnil))))))).subperm
  have hac : IsAcyclic multiRawRef := by rw [isAcyclic_iff]; decide
  have hperm :
      multiRawEs.Perm (multiRawRef ++ [⟨1, 1, 1⟩, ⟨0, 1, 9⟩, ⟨0, 2, 8⟩, ⟨3, 0, 6⟩]) := by
    simpa only [multiRawEs, multiRawRef, List.cons_append, List.nil_append] using
      (List.perm_append_comm (l₁ := [⟨1, 1, 1⟩, ⟨0, 1, 9⟩]) (l₂ := multiRawRef)).append_right
        [⟨0, 2, 8⟩, ⟨3, 0, 6⟩]
  have hpart : edgePartition multiRawRef = edgePartition multiRawEs := by
    rw [Perm.edgePartition_eq hperm]
    dsimp only [edgePartition]
    rw [edgePartitionFrom_append]
    simp only [edgePartitionFrom_cons, edgePartitionFrom_nil]
    rw [DisjointSet.Partition.merge_of_rel (by decide),
      DisjointSet.Partition.merge_of_rel (by decide),
      DisjointSet.Partition.merge_of_rel (by decide),
      DisjointSet.Partition.merge_of_rel (by decide)]
  refine ⟨⟨hsub, hac, hpart⟩, fun G' hG' => ?_⟩
  have hc_eq : (edgePartition G').numComponents = 2 := by rw [hG'.2.2, ← hpart]; decide
  have hlen : G'.length = 3 := by have ha := (isAcyclic_iff G').mp hG'.2.1; omega
  have hwt3 : ∀ e ∈ G', 3 ≤ e.weight := by
    intro e he
    have he_mem := hG'.1.subset he
    simp only [multiRawEs, List.mem_cons, List.not_mem_nil, or_false] at he_mem
    rcases he_mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exfalso
      have ha := isAcyclic_sublist (List.singleton_sublist.mpr he) hG'.2.1
      rw [isAcyclic_iff] at ha
      simp only [edgePartition, edgePartitionFrom_cons, edgePartitionFrom_nil,
        List.length_singleton] at ha
      have hself : (DisjointSet.Partition.discrete 5).rel (1 : Fin 5) 1 = true :=
        (DisjointSet.Partition.discrete 5).refl 1
      rw [DisjointSet.Partition.merge_of_rel hself] at ha
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
  have hbd := hsum G' hwt3
  have htot9 : totalWeight multiRawRef = 9 := by decide
  omega

private theorem multiRaw_msf_summary {msfEs : List (WeightedEdge 5 ℕ)}
    (hmsf : IsMinSpanningForest multiRawEs msfEs) :
    msfEs.length = 3 ∧ totalWeight msfEs = 9 := by
  have hc_eq : (edgePartition msfEs).numComponents = 2 := by
    rw [hmsf.1.2.2, ← multiRawRef_isMSF.1.2.2]; decide
  have hlen3 : msfEs.length = 3 := by have ha := (isAcyclic_iff msfEs).mp hmsf.1.2.1; omega
  have htot9 : totalWeight msfEs = 9 := by
    have h1 := hmsf.2 multiRawRef multiRawRef_isMSF.1
    have h2 := multiRawRef_isMSF.2 msfEs hmsf.1
    have h3 : totalWeight multiRawRef = 9 := by decide
    omega
  exact ⟨hlen3, htot9⟩

private theorem multiRawEs_fit : ∀ e ∈ multiRawEs, Fits 24 e.weight := fun e he => by
  simp only [multiRawEs, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact fits24_of_le (by decide)

private theorem multiRaw_prog_spec_witness :
    let s := Memory.State.init (encode multiRawEs)
    let prog := optimalMSFProg ⟨5, 7⟩
    let outBase := (Memory.spec 0).clientResult s prog
    let s' := (Memory.spec 0).clientState s prog
    optimalMSFSafe 24 ⟨5, 7⟩ s ∧
    (Memory.spec 24).ValidHistory s ((Memory.spec 24).clientHistory s prog) ∧
    ∃ msfEs : List (WeightedEdge 5 ℕ),
      IsMinSpanningForest multiRawEs msfEs ∧
      msfEs.length = 3 ∧
      totalWeight msfEs = 9 ∧
      outputList s'.mem outBase = encodeEdges msfEs ∧
      Fits 24 (outBase + 3 * msfEs.length) := by
  have hfit : Fits 24 (optimalMSFWordBound 5 multiRawEs.length) :=
    fits24_wordBound (by omega) (by decide)
  have hspec := optimalMSFProg_spec (w := 24) (n := 5) multiRawEs multiRawEs_fit hfit
  have hlen7 : multiRawEs.length = 7 := rfl
  rw [hlen7] at hspec
  obtain ⟨hsafe, hv, msfEs, hmsf, _, hout, hfit_out, _⟩ := hspec
  obtain ⟨hlen3, htot9⟩ := multiRaw_msf_summary hmsf
  exact ⟨hsafe, hv, msfEs, hmsf, hlen3, htot9, hout, hfit_out⟩

private theorem multiRaw_wordRAM_spec_witness :
    ∃ r C : ℕ, ∃ prog : Program .standard r, ¬prog.ReadsWidth ∧ prog.IsRandFree ∧
      ∃ steps : ℕ, ∃ msfEs : List (WeightedEdge 5 ℕ),
        ExecutesList 24 prog (State.init (encode multiRawEs))
          (encodeEdges msfEs) steps ∧
        IsMinSpanningForest multiRawEs msfEs ∧
        msfEs.length = 3 ∧
        totalWeight msfEs = 9 ∧
        steps ≤ C * (optDepthMN 7 5 + 7 + 5 + 1) := by
  obtain ⟨r, C, prog, hnw, hrf, hspec⟩ := optimalMSF_wordRAM_spec
  have hfit : Fits 24 (optimalMSFWordBound 5 multiRawEs.length) :=
    fits24_wordBound (by omega) (by decide)
  have h := hspec 5 multiRawEs 24 multiRawEs_fit hfit
  have hlen7 : multiRawEs.length = 7 := rfl
  rw [hlen7] at h
  obtain ⟨steps, msfEs, hex, hmsf, hsteps⟩ := h
  obtain ⟨hlen3, htot9⟩ := multiRaw_msf_summary hmsf
  exact ⟨r, C, prog, hnw, hrf, steps, msfEs, hex, hmsf, hlen3, htot9, hsteps⟩

/-! ## 3. Connected `SimpleGraph (Fin 4)` `IsMST` specialization -/

private def k4Wt (z : Sym2 (Fin 4)) : ℕ :=
  if z = s(0, 1) then 2
  else if z = s(1, 2) then 3
  else if z = s(2, 3) then 4
  else 10

private theorem k4_connected : (⊤ : SimpleGraph (Fin 4)).Connected := by
  refine (SimpleGraph.connected_iff_exists_forall_reachable _).mpr ⟨0, fun v => ?_⟩
  fin_cases v
  · exact SimpleGraph.Reachable.refl 0
  all_goals exact SimpleGraph.Adj.reachable (by decide)

private theorem k4Wt_fit : ∀ e ∈ graphEdges (⊤ : SimpleGraph (Fin 4)) k4Wt, Fits 24 e.weight := by
  intro e he
  rw [((mem_graphEdges _ _ e).mp he).2.2]
  exact fits24_of_le (by dsimp only [k4Wt]; split_ifs <;> decide)

private theorem k4_isMST_witness :
    ∃ r C : ℕ, ∃ prog : Program .standard r, ¬prog.ReadsWidth ∧ prog.IsRandFree ∧
      ∃ steps : ℕ, ∃ msfEs : List (WeightedEdge 4 ℕ),
        ExecutesList 24 prog
          (State.init (encode (graphEdges (⊤ : SimpleGraph (Fin 4)) k4Wt)))
          (encodeEdges msfEs) steps ∧
        (⊤ : SimpleGraph (Fin 4)).IsMST k4Wt (toSimpleGraph msfEs) ∧
        steps ≤ C * (optDepthMN (⊤ : SimpleGraph (Fin 4)).edgeFinset.card 4 + 1) := by
  obtain ⟨r, C, prog, hnw, hrf, hspec⟩ := optimalMSF_simpleGraph_isMST_spec
  have hfit : Fits 24 (optimalMSFWordBound 4 (⊤ : SimpleGraph (Fin 4)).edgeFinset.card) := by
    rw [show (⊤ : SimpleGraph (Fin 4)).edgeFinset.card = 6 by decide]
    exact fits24_wordBound (by omega) (by decide)
  obtain ⟨steps, msfEs, hex, hmst, hsteps⟩ :=
    hspec 4 (⊤ : SimpleGraph (Fin 4)) k4Wt 24 k4_connected k4Wt_fit hfit
  exact ⟨r, C, prog, hnw, hrf, steps, msfEs, hex, hmst, hsteps⟩

private theorem k4_isMST_from_prog_spec :
    let es := graphEdges (⊤ : SimpleGraph (Fin 4)) k4Wt
    ∃ msfEs : List (WeightedEdge 4 ℕ),
      (⊤ : SimpleGraph (Fin 4)).IsMST k4Wt (toSimpleGraph msfEs) ∧
      outputList ((Memory.spec 0).clientState (Memory.State.init (encode es))
        (optimalMSFProg ⟨4, es.length⟩)).mem
        ((Memory.spec 0).clientResult (Memory.State.init (encode es))
          (optimalMSFProg ⟨4, es.length⟩)) = encodeEdges msfEs := by
  have hfit : Fits 24 (optimalMSFWordBound 4
      (graphEdges (⊤ : SimpleGraph (Fin 4)) k4Wt).length) := by
    rw [length_graphEdges, show (⊤ : SimpleGraph (Fin 4)).edgeFinset.card = 6 by decide]
    exact fits24_wordBound (by omega) (by decide)
  obtain ⟨_, _, msfEs, hmsf, _, hout, _, _⟩ := optimalMSFProg_spec (w := 24) _ k4Wt_fit hfit
  exact ⟨msfEs, isMST_toSimpleGraph_of_isMinSpanningForest k4_connected hmsf, hout⟩

/-! ## 4. Direct `Program .standard` lowering via `realizes_optimalMSFProg` -/

private theorem exists_standard_optimalMSFProg_oneEdge_halts :
    ∃ r C pc : ℕ, ∃ prog : Program .standard r, ¬prog.ReadsWidth ∧ prog.IsRandFree ∧
      ∃ y n,
        Runs 24 prog (State.init (encode oneEdgeRawEs)) ⟨pc, y⟩ n ∧
        ∃ outBase : ℕ,
          step 24 prog ⟨pc, y⟩ = .halt outBase ∧
          outputList y.mem outBase = [0, 2, 7] ∧
          n + 1 ≤ C * (memoryCost (optimalMSFProg ⟨3, 1⟩)
            (Memory.State.init (encode oneEdgeRawEs)) + 3 * (Nat.log 2 3 + 3) + 3) + 1 := by
  obtain ⟨r, C, pc, prog₀, hnw₀, frontier, _, hrun⟩ :=
    realizes_optimalMSFProg.exists_standard_basis_init_program_state_from_words (0 : Fin 1)
  have hlayout : ∀ j : Fin 2, (encode oneEdgeRawEs).getD j.val 0 =
      WordEncoding.encode (⟨3, 1⟩ : OptimalMSFArgs) j := fun j => by fin_cases j <;> rfl
  set s := Memory.State.init (encode oneEdgeRawEs)
  set prog := optimalMSFProg ⟨3, 1⟩
  obtain ⟨hsafe, hv, _, hout, _, _⟩ := oneEdge_msf_witness
  have hin : InputFits 24 (encode oneEdgeRawEs) :=
    inputFits_encode oneEdgeRawEs (fits24_of_le (by decide)) fun e he => by
      simp only [oneEdgeRawEs, List.mem_singleton] at he; rw [he]; exact fits24_of_le (by decide)
  obtain ⟨y, n, hruns, hhalt, hmem, _, hsteps⟩ :=
    hrun 24 ⟨3, 1⟩ (encode oneEdgeRawEs) hlayout (by rw [length_encode]; decide)
      (by rw [length_encode]; exact fits24_of_le (by decide)) hin hsafe hv
  have hres_w := clientResult_width 24 prog s
  have hst_w := clientState_width 24 prog s
  have hout_y : outputList y.mem
      (WordEncoding.encode (α := ℕ) ((Memory.spec 24).clientResult s prog) 0) = [0, 2, 7] := by
    have hmy : y.mem = ((Memory.spec 0).clientState s prog).mem := by
      change (memoryState frontier y).mem = _; rw [hmem, hst_w]
    change outputList y.mem ((Memory.spec 24).clientResult s prog) = _
    rw [hres_w, hmy, hout]
  refine ⟨r, C, pc, stripRand prog₀, not_readsWidth_stripRand hnw₀, isRandFree_stripRand prog₀,
    y, n, runs_stripRand hruns, _, step_stripRand_of_halt hhalt, hout_y, ?_⟩
  dsimp only at hsteps
  have hle_eq : memoryCost (optimalMSFProg ⟨3, 1⟩) (Memory.State.init (encode oneEdgeRawEs)) +
      (3 * (Nat.log 2 3 + 3) + (1 + 1)) + 1 =
      memoryCost prog s + 3 * (Nat.log 2 3 + 3) + 3 := by
    change memoryCost prog s + (3 * (Nat.log 2 3 + 3) + (1 + 1)) + 1 = _
    omega
  rwa [hle_eq] at hsteps

end CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.OptimalMSFDriver
