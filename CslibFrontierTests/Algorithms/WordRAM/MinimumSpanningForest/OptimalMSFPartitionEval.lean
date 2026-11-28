/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.OptimalMSF.PartitionEval
import CslibFrontier.Computability.WordRAM.Realization.Program.Standard
import CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.GraphOpsTestSupport
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

/-!
# Client Tests for `OptimalMSF.PartitionEval`

Exercises `pr02EvalDTLoop`, `pr02EvalDTLoop_spec`, `realizes_pr02EvalDTLoop`, `pr02SolveHRemProg`,
`pr02SolveHRemProg_spec`, `realizes_pr02SolveHRemProg`, `EvalDTLoopArgs`, `SolveHRemArgs`, and
`SolveHRemResult` on
empty and non-empty `r0 = 2` runs and composite `Program .standard` lowering.
-/
-- This test module intentionally exports no declarations.
set_option linter.privateModule false

namespace CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.OptimalMSFPartitionEval

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.DisjointSet Cslib.Algorithms.Lean.Kruskal
open Cslib.Query.MinimumSpanningForest Cslib.Algorithms.WordRAM.MinimumSpanningForest
open CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.GraphOpsTestSupport

/-! ## 1. Decision-Tree Table (`r0 = 2`) and Partition-Round Test Fixtures -/

private theorem fin2_leaf_correct {e : ℕ} (he : e ≤ 1) {ends : Fin e → Sym2 (Fin 2)}
    (hsimp : IsSimple ends) :
    MSFDT.Correct ends (.leaf (Finset.univ : Finset (Fin e))) ∧ optDepth ends = 0 := by
  have hcorr : MSFDT.Correct ends (.leaf (Finset.univ : Finset (Fin e))) := by
    rw [MSFDT.correct_iff]; intro p; dsimp only [MSFTree.eval]
    rw [eq_comm, Finset.eq_univ_iff_forall]; intro x; induction hx : ends x using Sym2.ind with
    | _ a b =>
      rw [Cslib.Multigraph.mem_msf_iff p hx]; refine ⟨Finset.mem_univ _, fun hc => ?_⟩
      have hemp : {f | f ∈ (Finset.univ : Finset (Fin e)) ∧ p f < p x} = ∅ := by
        ext f; simp only [Set.mem_ofPred_eq, Finset.mem_univ, true_and, Set.mem_empty_iff_false,
          iff_false, not_lt]; have : f = x := Fin.ext (by omega); subst this; exact le_rfl
      rw [hemp, Cslib.Multigraph.joins_empty_iff] at hc; subst hc
      exact ((isSimple_iff _).mp hsimp).1 x (hx ▸ Sym2.mk_isDiag_iff.mpr rfl)
  exact ⟨hcorr, Nat.eq_zero_of_le_zero (optDepth_le_of_correct hcorr)⟩

private def dtTable2Words (base : ℕ) : List ℕ := [base + 2, base + 5, 0, 0, 0, 1, 0, 0, 1]

private theorem dtTable2_holds_and_bounds (base : ℕ) (mem : ℕ → ℕ)
    (hmem : ∀ i : Fin 9, mem (base + i.val) = (dtTable2Words base).getD i.val 0) :
    HoldsDTTable 2 base mem ∧ DTTableInBounds 2 base (base + 9) mem := by
  have hm0 : (maskEdgePairs 2 0).length = 0 := by decide
  have hm1 : (maskEdgePairs 2 1).length = 1 := by decide
  have hpow : 2 ^ Nat.choose 2 2 = 2 := by decide
  have h0 : mem base = base + 2 := hmem 0; have h1 : mem (base + 1) = base + 5 := hmem 1
  have h2 : mem (base + 2) = 0 := hmem 2; have h3 : mem (base + 3) = 0 := hmem 3
  have h4 : mem (base + 4) = 0 := hmem 4; have h5 : mem (base + 5) = 1 := hmem 5
  have h6 : mem (base + 6) = 0 := hmem 6; have h7 : mem (base + 7) = 0 := hmem 7
  have h8 : mem (base + 8) = 1 := hmem 8
  refine ⟨(holdsDTTable_iff _ _ _).mpr fun mask hmask => ?_,
    (dtTableInBounds_iff _ _ _ _).mpr ⟨by omega, fun mask hmask => ?_⟩⟩
  · rw [hpow] at hmask; interval_cases mask
    · have hc := fin2_leaf_correct (e := (maskEdgePairs 2 0).length) (by omega)
        (endsOfMask_isSimple 2 0)
      refine ⟨by simp only [Nat.add_zero, h0, h2, hm0], by simp only [Nat.add_zero, h0, h3, hc.2],
        fun j hj => by rw [hm0] at hj; omega, .leaf Finset.univ,
        by simp only [Nat.add_zero, h0, h3]; exact MSFTree.isComplete_leaf, hc.1, ?_⟩
      simp only [Nat.add_zero, h0, h3, hm0, holdsCompleteTree_leaf]
      exact ⟨by decide, by decide, by
        rw [show base + 2 + 2 + 0 + 2 * (2 ^ 0 - 1) + (1 - 2 ^ 0) = base + 4 by omega, h4]; decide⟩
    · have hc := fin2_leaf_correct (e := (maskEdgePairs 2 1).length) (by omega)
        (endsOfMask_isSimple 2 1)
      refine ⟨by rw [h1, h5, hm1], by rw [h1, h6, hc.2], fun j hj => ?_, .leaf Finset.univ,
        by rw [h1, h6]; exact MSFTree.isComplete_leaf, hc.1, ?_⟩
      · obtain rfl : j = 0 := by rw [hm1] at hj; omega
        rw [h1, show base + 5 + 2 + 0 = base + 7 by omega, h7]; decide +revert
      · rw [h1, h6, hm1, holdsCompleteTree_leaf]; refine ⟨by decide, by decide, ?_⟩
        rw [show base + 5 + 2 + 1 + 2 * (2 ^ 0 - 1) + (1 - 2 ^ 0) = base + 8 by omega, h8]; decide
  · rw [hpow] at hmask
    interval_cases mask <;> [simp only [Nat.add_zero, h0, hm0, h3]; simp only [h1, hm1, h6]] <;>
      omega

private def singleEdgeTree4 (a b : Fin 4) (wt : ℕ) (hne : a ≠ b) : DynamicDJPTree 4 where
  numSteps := 1; root := a; edge _ := ⟨a, b, wt⟩; wPop _ := wt; vIn _ := a; vOut _ := b
  edge_weight_le_wPop s := by fin_cases s; exact le_rfl
  ends_match s := by fin_cases s; simp
  vIn_mem s := by fin_cases s; simp [djpVerts]
  vOut_not_mem s := by fin_cases s; simpa [djpVerts] using hne.symm
  djp_future s s' hlt := by fin_cases s; fin_cases s'; exact absurd hlt (by decide)

private def r4_0 : PartitionRoundWitness 4 where
  tree := singleEdgeTree4 0 1 5 (by decide); numVerts := 2
  lift k := if k.val = 0 then 1 else 0; compLocal := [⟨1, 0, 5, 10⟩]; corrEdges := [⟨1, 2, 9, 99⟩]
private def r4_1 : PartitionRoundWitness 4 where
  tree := singleEdgeTree4 2 3 3 (by decide); numVerts := 2
  lift k := if k.val = 0 then 2 else 3; compLocal := [⟨0, 1, 3, 20⟩]; corrEdges := []
private def rounds4 : List (PartitionRoundWitness 4) := [r4_0, r4_1]
private def hRem4 : List (IndexedEdge 4) := [⟨0, 2, 9, 101⟩, ⟨1, 3, 4, 102⟩, ⟨0, 3, 7, 103⟩]
private def es4 : List (IndexedEdge 4) := [⟨0, 1, 5, 10⟩, ⟨2, 3, 3, 20⟩] ++ hRem4 ++ [⟨1, 2, 9, 99⟩]
private def conglomFn4 (x : Fin 4) : Fin 2 := if x.val < 2 then 0 else 1

private theorem es4_isSimple : IsSimple (edgeEnds (es4.map IndexedEdge.toWeighted)) :=
  (isSimple_iff _).mpr ⟨fun i => by fin_cases i <;> decide,
    fun i j hij => by fin_cases i <;> fin_cases j <;> first | rfl | exact absurd hij (by decide)⟩
private theorem rounds4_cov : ∀ x : Fin 4, ∃ r ∈ rounds4, x ∈ r.verts := fun x => by
  fin_cases x <;>
    first | exact ⟨r4_0, by simp [rounds4], by decide⟩ | exact ⟨r4_1, by simp [rounds4], by decide⟩
private theorem rounds4_conglom_rel : ∀ x y : Fin 4, conglomFn4 x = conglomFn4 y ↔
    (edgePartition (rounds4.flatMap fun r => r.tree.treeEdges)).rel x y = true := fun x y => by
  fin_cases x <;> fin_cases y <;> decide

private theorem rounds4_stop : ∀ i : Fin rounds4.length,
    2 ≤ (rounds4[i.val]'i.isLt).verts.card ∨ (∃ j : Fin rounds4.length, j.val < i.val ∧
      ((rounds4[i.val]'i.isLt).verts ∩ (rounds4[j.val]'j.isLt).verts).Nonempty) ∨
    (∀ j : Fin rounds4.length, j ≠ i →
      ¬((rounds4[i.val]'i.isLt).verts ∩ (rounds4[j.val]'j.isLt).verts).Nonempty) ∧
    ∀ e ∈ hRem4, e.u ∉ (rounds4[i.val]'i.isLt).verts ∧ e.v ∉ (rounds4[i.val]'i.isLt).verts := by
  intro i; fin_cases i <;> exact Or.inl (by decide)

private theorem rounds4_inter (i : Fin rounds4.length) :
    ((rounds4[i.val]'i.isLt).verts ∩ (Finset.univ.filter fun j : Fin rounds4.length =>
      j.val < i.val).biUnion (fun j => rounds4[j.val].verts)).card ≤ 1 := by fin_cases i <;> decide

private theorem singleton_msf_eq {n : ℕ} {e : IndexedEdge n} (hne : e.u ≠ e.v)
    {F : List (IndexedEdge n)} (hsub : F.Subperm [e])
    (hmsf : IsMinSpanningForest ([e].map IndexedEdge.toWeighted) (F.map IndexedEdge.toWeighted)) :
    F = [e] := by
  rcases F with _ | ⟨x, r⟩
  · have h1 : (edgePartition ([e].map IndexedEdge.toWeighted)).rel e.u e.v = true := by
      simp [edgePartition, IndexedEdge.toWeighted]
    rw [← hmsf.1.2.2] at h1; simp only [List.map_nil, edgePartition, edgePartitionFrom_nil] at h1
    exact absurd (Partition.rel_discrete_eq_true.mp h1) hne
  · have hlen := hsub.length_le; simp only [List.length_cons, List.length_nil] at hlen
    obtain rfl : r = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hx := hsub.subset List.mem_cons_self; simp only [List.mem_singleton] at hx; subst hx; rfl

private def evalLoopBlock4 (tBase : ℕ) : List ℕ :=
  dtTable2Words tBase ++ encodeIndexedEdges r4_0.compLocal ++ encodeIndexedEdges r4_1.compLocal ++
    [1, 0, 2, 3, 2, 1, tBase + 9, 2, 1, tBase + 13, tBase + 17, tBase + 19] ++ List.replicate 16 0

private theorem rounds4_eval_cert {tBase : ℕ} {s : Memory.State} (hwf : Memory.WellFormed 16 s)
    (hfr : tBase + 45 ≤ s.frontier) (hfit : Fits 16 (s.frontier + 42))
    (hblk : (List.range 29).map (fun i => s.mem (tBase + i)) = (evalLoopBlock4 tBase).take 29) :
    pr02EvalDTLoopSafe 16 ⟨2, tBase, tBase + 21, tBase + 27, tBase + 29⟩ s ∧
    Memory.FramedTriple 16 s (pr02EvalDTLoop ⟨2, tBase, tBase + 21, tBase + 27, tBase + 29⟩)
      (25 * 6 + 15 * optDepthMN 6 4 + 20 * 4) (Set.Ico (tBase + 29) (tBase + 45))
      fun fcLen s' => fcLen = 2 ∧ s.frontier ≤ s'.frontier ∧ s'.frontier ≤ s.frontier + 42 ∧
        Memory.WellFormed 16 s' ∧
        HoldsIndexedEdges (tBase + 29) ([⟨0, 1, 5, 10⟩, ⟨2, 3, 3, 20⟩] : List (IndexedEdge 4))
          s'.mem := by
  let L : List ℕ := [tBase + 2, tBase + 5, 0, 0, 0, 1, 0, 0, 1, 1, 0, 5, 10, 0, 1, 3, 20, 1, 0, 2,
    3, 2, 1, tBase + 9, 2, 1, tBase + 13, tBase + 17, tBase + 19]
  have hblk' := hblk
  rw [show (evalLoopBlock4 tBase).take 29 = L by
    simp [L, evalLoopBlock4, dtTable2Words, encodeIndexedEdges, r4_0, r4_1]] at hblk'
  have hget : ∀ k (hk : k < 29), s.mem (tBase + k) = L.getD k 0 := fun k hk => by
    have h1 := congrArg (fun l : List ℕ => l.getD k 0) hblk'
    rwa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk,
      Option.map_some, Option.getD_some] at h1
  obtain ⟨htab, hbnd⟩ := dtTable2_holds_and_bounds tBase s.mem fun i => by
    fin_cases i <;> first
      | exact hget 0 (by decide) | exact hget 1 (by decide) | exact hget 2 (by decide)
      | exact hget 3 (by decide) | exact hget 4 (by decide) | exact hget 5 (by decide)
      | exact hget 6 (by decide) | exact hget 7 (by decide) | exact hget 8 (by decide)
  have hed0 : HoldsIndexedEdges (tBase + 9) r4_0.compLocal s.mem := fun j hj => by
    have : j = 0 := by simpa [r4_0] using hj
    subst this; simp only [r4_0, List.getElem_cons_zero, Nat.mul_zero, Nat.add_zero, Nat.add_assoc]
    exact ⟨hget 9 (by decide), hget 10 (by decide), hget 11 (by decide), hget 12 (by decide)⟩
  have hed1 : HoldsIndexedEdges (tBase + 13) r4_1.compLocal s.mem := fun j hj => by
    have : j = 0 := by simpa [r4_1] using hj
    subst this; simp only [r4_1, List.getElem_cons_zero, Nat.mul_zero, Nat.add_zero, Nat.add_assoc]
    exact ⟨hget 13 (by decide), hget 14 (by decide), hget 15 (by decide), hget 16 (by decide)⟩
  have hrl : rounds4.length = 2 := rfl
  have hspec := @pr02EvalDTLoop_spec 16 2 (tBase + 9) 4 6 rounds4 hRem4 es4
    tBase (tBase + 21) (tBase + 27) (tBase + 29) s (by decide) hwf es4_isSimple
    (List.Perm.refl _) (by decide) (by decide) htab hbnd (by omega)
    (by rw [hrl]; omega) (by rw [hrl]) (by omega)
    { numVerts_eq := fun i => by
        fin_cases i
        · exact hget 21 (by decide)
        · exact hget 24 (by decide)
      numEdges_eq := fun i => by
        fin_cases i
        · exact hget 22 (by decide)
        · exact hget 25 (by decide)
      holdsEdges := fun i => by
        fin_cases i
        · change HoldsIndexedEdges (s.mem (tBase + 23)) r4_0.compLocal s.mem
          rw [hget 23 (by decide)]; exact hed0
        · change HoldsIndexedEdges (s.mem (tBase + 26)) r4_1.compLocal s.mem
          rw [hget 26 (by decide)]; exact hed1
      lift_eq := fun i k => by
        fin_cases i
        · change s.mem (s.mem (tBase + 27) + k.val) = (r4_0.lift k).val
          rw [hget 27 (by decide)]
          fin_cases k <;> [exact hget 17 (by decide); exact hget 18 (by decide)]
        · change s.mem (s.mem (tBase + 28) + k.val) = (r4_1.lift k).val
          rw [hget 28 (by decide)]
          fin_cases k <;> [exact hget 19 (by decide); exact hget 20 (by decide)]
      numVerts_le := fun i => by fin_cases i <;> decide
      numVerts_le_two_mul := fun i _ => by fin_cases i <;> decide
      lift_injective := fun i a b h => by
        fin_cases i <;> fin_cases a <;> fin_cases b <;> cases h <;> rfl
      isSimple := fun i =>
        (isSimple_iff _).mpr ⟨fun k => by
            fin_cases i <;> [dsimp only [rounds4, r4_0]; dsimp only [rounds4, r4_1]] <;>
              fin_cases k <;> decide,
          fun a b _ => by fin_cases i <;> fin_cases a <;> fin_cases b <;> rfl⟩
      compGlobal_verts := fun i e he => by
        fin_cases i
        · change e ∈ r4_0.compGlobal at he
          simp only [r4_0, PartitionRoundWitness.compGlobal, List.map_cons,
            List.map_nil, List.mem_singleton] at he
          subst he; decide
        · change e ∈ r4_1.compGlobal at he
          simp only [r4_1, PartitionRoundWitness.compGlobal, List.map_cons,
            List.map_nil, List.mem_singleton] at he
          subst he; decide
      inter_prev_card_le_one := rounds4_inter }
    (fun i => by
      fin_cases i
      · change s.mem (tBase + 23) + 4 * 1 ≤ tBase + 29 ∧ s.mem (tBase + 27) + 2 ≤ tBase + 29
        rw [show s.mem (tBase + 23) = tBase + 9 from hget 23 (by decide),
          show s.mem (tBase + 27) = tBase + 17 from hget 27 (by decide)]
        omega
      · change s.mem (tBase + 26) + 4 * 1 ≤ tBase + 29 ∧ s.mem (tBase + 28) + 2 ≤ tBase + 29
        rw [show s.mem (tBase + 26) = tBase + 13 from hget 26 (by decide),
          show s.mem (tBase + 28) = tBase + 19 from hget 28 (by decide)]
        omega)
    (hfit.of_le (by omega))
  refine ⟨hspec.1, hspec.2.frame_mono (fun _ hx => by simp only [Set.mem_Ico] at hx ⊢; omega)
    |>.mono le_rfl fun fcLen s' ⟨_, hs_s', hs'_fr, hwf', F_comps, hlen, hflat, hholds, hmsf⟩ => ?_⟩
  rcases F_comps with _ | ⟨F0, _ | ⟨F1, _ | _⟩⟩
  · simp only [List.length_nil, List.length_cons, rounds4] at hlen; omega
  · simp only [List.length_cons, List.length_nil, rounds4] at hlen; omega
  case cons.cons.cons => simp only [List.length_cons, List.length_nil, rounds4] at hlen; omega
  obtain ⟨h0_sub, h0_msf⟩ := hmsf ⟨0, by decide⟩; obtain ⟨h1_sub, h1_msf⟩ := hmsf ⟨1, by decide⟩
  obtain rfl : F0 = [⟨0, 1, 5, 10⟩] := singleton_msf_eq (by decide) h0_sub h0_msf
  obtain rfl : F1 = [⟨2, 3, 3, 20⟩] := singleton_msf_eq (by decide) h1_sub h1_msf
  exact ⟨by rw [← hflat]; rfl, hs_s', by omega, hwf', by simpa using hholds⟩

/-! ## 2. Concrete Runs of `pr02EvalDTLoop` -/

example :
    let s := Memory.State.init (dtTable2Words 1 ++ List.replicate 8 0)
    let env : EvalDTLoopArgs := ⟨0, 1, 10, 10, 10⟩
    pr02EvalDTLoopSafe 16 env s ∧ (Memory.spec 0).clientResult s (pr02EvalDTLoop env) = 0 ∧
    ((Memory.spec 0).clientState s (pr02EvalDTLoop env)).frontier ≤ 18 ∧
    ∀ a < 10, ((Memory.spec 0).clientState s (pr02EvalDTLoop env)).mem a = s.mem a := by
  intro s env
  have hwf : Memory.WellFormed 16 s := Memory.wellFormed_init (by decide) (by decide)
  obtain ⟨htab, hbnd⟩ := dtTable2_holds_and_bounds 1 s.mem fun i => by fin_cases i <;> decide
  have hspec := @pr02EvalDTLoop_spec 16 2 10 2 0 [] [] [] 1 10 10 10 s (by decide) hwf
    ((isSimple_iff _).mpr ⟨fun j => Fin.elim0 j, fun a => Fin.elim0 a⟩) (List.Perm.refl _)
    (by decide) (by decide) htab hbnd (by decide) (by decide) (by decide) (by decide)
    ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i,
      fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i,
      fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩ (fun i => Fin.elim0 i) (by decide)
  obtain ⟨_, _, hmod, _, _, hfr, _, F_comps, hlen, hflat, _, _⟩ :=
    framedTriple_iff_realization.mp hspec.2
  obtain rfl : F_comps = [] := List.eq_nil_of_length_eq_zero hlen
  exact ⟨hspec.1, hflat.symm, hfr, fun a ha =>
    hmod.mem_eq_of_not_mem (by change a < 18; omega) (by simp only [Set.mem_Ico]; omega)⟩

example :
    let s := Memory.State.init (evalLoopBlock4 1)
    let env : EvalDTLoopArgs := ⟨2, 1, 22, 28, 30⟩
    let s' := (Memory.spec 0).clientState s (pr02EvalDTLoop env)
    pr02EvalDTLoopSafe 16 env s ∧ (Memory.spec 0).clientResult s (pr02EvalDTLoop env) = 2 ∧
    readIndexedEdges 30 2 s'.mem = [(0, 1, 5, 10), (2, 3, 3, 20)] ∧
    ∀ a < 30, s'.mem a = s.mem a := by
  intro s env s'
  have hwf : Memory.WellFormed 16 s := Memory.wellFormed_init (by decide) (by decide)
  obtain ⟨hsafe, hft⟩ := rounds4_eval_cert (tBase := 1) hwf (by decide) (by decide) (by decide)
  obtain ⟨_, _, hmod, hfc2, _, _, _, hholds⟩ := framedTriple_iff_realization.mp hft
  obtain ⟨h00, h01, h02, h03⟩ := hholds 0 (by decide)
  obtain ⟨h10, h11, h12, h13⟩ := hholds 1 (by decide)
  refine ⟨hsafe, hfc2, ?_, fun a ha =>
    hmod.mem_eq_of_not_mem (by change a < 46; omega) (by simp only [Set.mem_Ico]; omega)⟩
  simp only [readIndexedEdges, List.range_succ, List.range_zero, List.nil_append,
    List.singleton_append, List.map_cons, List.map_nil]; rw [h00, h01, h02, h03, h10, h11, h12, h13]
  rfl

/-! ## 3. Concrete Runs of `pr02SolveHRemProg` -/

example :
    let s := Memory.State.init [0, 0, 1, 1]
    let d : SolveHRemArgs := ⟨2, 5, 0, 1⟩
    let res := (Memory.spec 0).clientResult s (pr02SolveHRemProg d)
    let s' := (Memory.spec 0).clientState s (pr02SolveHRemProg d)
    pr02SolveHRemProgSafe 16 d s ∧ res.numEdges = 0 ∧ res.edgeBase ≤ s'.frontier ∧
    5 ≤ s'.frontier ∧ s'.frontier ≤ 6124 ∧ ∀ a < 5, s'.mem a = s.mem a := by
  intro s d res s'
  have hwf : Memory.WellFormed 16 s := Memory.wellFormed_init (by decide) (by decide)
  have hspec := @pr02SolveHRemProg_spec 16 4 2 4 2 5 1 rounds4 [] conglomFn4 s (by decide) hwf
    (le_refl 4) (by decide) (by decide) (fun _ hi => absurd hi (Nat.not_lt_zero _)) (by decide)
    (fun u => by dsimp only [s]; fin_cases u <;> decide) (by decide) rounds4_cov
    rounds4_conglom_rel (fun i => by fin_cases i <;> exact Or.inl (by decide)) (by decide)
  change pr02SolveHRemProgSafe 16 d s ∧ Memory.FramedTriple 16 s (pr02SolveHRemProg d) _ ∅ _
    at hspec
  obtain ⟨_, _, hmod, hbase, _, hlen, hfr_ge, hfr_le, _⟩ := framedTriple_iff_realization.mp hspec.2
  have hnil : ([] : List (IndexedEdge 4)).length = 0 := rfl; have hs_fr : s.frontier = 5 := rfl
  change res.edgeBase + 4 * res.numEdges ≤ s'.frontier at hbase
  change s.frontier ≤ s'.frontier at hfr_ge
  change s'.frontier ≤ s.frontier + 341 * [].length + 1529 * 4 + 3 at hfr_le
  rw [hs_fr] at hfr_ge hfr_le; rw [hnil] at hfr_le
  exact ⟨hspec.1, Nat.eq_zero_of_le_zero (by rw [hnil] at hlen; exact hlen), by omega, hfr_ge,
    hfr_le, fun a ha => hmod.mem_eq_of_not_mem (hs_fr ▸ ha) (Set.notMem_empty a)⟩

private theorem hRem4_holds_of_eq {base : ℕ} {mem : ℕ → ℕ}
    (hmem : (List.range 12).map (fun i => mem (base + i)) = encodeIndexedEdges hRem4) :
    HoldsIndexedEdges base hRem4 mem := by
  rw [show encodeIndexedEdges hRem4 = [0, 2, 9, 101, 1, 3, 4, 102, 0, 3, 7, 103] by
    simp [encodeIndexedEdges, hRem4]] at hmem
  have hget : ∀ k (hk : k < 12), mem (base + k) =
      ([0, 2, 9, 101, 1, 3, 4, 102, 0, 3, 7, 103] : List ℕ).getD k 0 := fun k hk => by
    have h1 := congrArg (fun l : List ℕ => l.getD k 0) hmem
    rwa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk,
      Option.map_some, Option.getD_some] at h1
  intro j hj; have hj3 : j < 3 := by simpa [hRem4] using hj
  interval_cases j <;> dsimp only [hRem4, List.getElem_cons_zero, List.getElem_cons_succ]
  · simp only [Nat.mul_zero, Nat.add_zero]
    exact ⟨hget 0 (by decide), hget 1 (by decide), hget 2 (by decide), hget 3 (by decide)⟩
  · simp only [Nat.add_assoc]
    exact ⟨hget 4 (by decide), hget 5 (by decide), hget 6 (by decide), hget 7 (by decide)⟩
  · simp only [Nat.add_assoc]
    exact ⟨hget 8 (by decide), hget 9 (by decide), hget 10 (by decide), hget 11 (by decide)⟩

private theorem hLift4_unique {H_lift : List (IndexedEdge 4)} (hsub : H_lift.Subperm hRem4)
    (hmsf : IsMinSpanningForest (contractEdgeList conglomFn4 (hRem4.map IndexedEdge.toWeighted))
      (contractEdgeList conglomFn4 (H_lift.map IndexedEdge.toWeighted))) :
    H_lift = [⟨1, 3, 4, 102⟩] := by
  have hlen := isAcyclic_length_le_finset_sub_one (Finset.univ : Finset (Fin 2)) _
    hmsf.1.2.1 (fun _ _ => ⟨Finset.mem_univ _, Finset.mem_univ _⟩)
  simp only [Finset.card_univ, Fintype.card_fin, contractEdgeList, List.length_map] at hlen
  rcases H_lift with _ | ⟨x, r⟩
  · have hrel := congrArg (fun p : Partition 2 => p.rel 0 1) hmsf.1.2.2; revert hrel; decide
  · have hr : r = [] :=
      List.eq_nil_of_length_eq_zero (by simp only [List.length_cons] at hlen; omega)
    subst hr; have hx := hsub.subset List.mem_cons_self
    simp only [hRem4, List.mem_cons, List.not_mem_nil, or_false] at hx
    have hsub1 : (contractEdgeList conglomFn4 ([⟨1, 3, 4, 102⟩].map IndexedEdge.toWeighted)).Subperm
        (contractEdgeList conglomFn4 (hRem4.map IndexedEdge.toWeighted)) := by
      simp only [contractEdgeList, hRem4, List.map_cons, List.map_nil]
      exact (List.singleton_sublist.mpr (by simp)).subperm
    rcases hx with rfl | rfl | rfl <;> try rfl
    all_goals have hopt := hmsf.2 _ ⟨hsub1, by rw [isAcyclic_iff]; decide, by decide⟩; simp only
      [totalWeight, contractEdgeList, conglomFn4, contractEdge, IndexedEdge.toWeighted,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hopt; omega

private theorem rounds4_hrem_cert {hRemBase conglomBase : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed 16 s) (hrem : HoldsIndexedEdges hRemBase hRem4 s.mem)
    (hrem_fr : hRemBase + 4 * 3 ≤ s.frontier) (hcong_fr : conglomBase + 4 ≤ s.frontier)
    (hcong : ∀ u : Fin 4, s.mem (conglomBase + u.val) = (conglomFn4 u).val)
    (hfit : Fits 16 (s.frontier + 341 * 3 + 1529 * 4 + 3)) :
    pr02SolveHRemProgSafe 16 ⟨2, hRemBase, 3, conglomBase⟩ s ∧
    ∃ C, Memory.FramedTriple 16 s (pr02SolveHRemProg ⟨2, hRemBase, 3, conglomBase⟩) C ∅
      fun res s' => res.edgeBase + 4 ≤ s'.frontier ∧ res.numEdges = 1 ∧
        HoldsIndexedEdges res.edgeBase ([⟨1, 3, 4, 102⟩] : List (IndexedEdge 4)) s'.mem := by
  have hspec := @pr02SolveHRemProg_spec 16 4 2 4 2 hRemBase conglomBase rounds4 hRem4 conglomFn4 s
    (by decide) hwf (le_refl 4) (by decide) (by decide) hrem hrem_fr hcong hcong_fr
    rounds4_cov rounds4_conglom_rel rounds4_stop hfit
  change pr02SolveHRemProgSafe 16 ⟨2, hRemBase, 3, conglomBase⟩ s ∧
    Memory.FramedTriple 16 s (pr02SolveHRemProg ⟨2, hRemBase, 3, conglomBase⟩) _ ∅ _ at hspec
  refine ⟨hspec.1, _, hspec.2.mono le_rfl fun res s' ⟨hbase, _, _, _, _, _, H_lift, hlen, hholds,
      hsub, hmsf⟩ => ?_⟩
  have huniq := hLift4_unique hsub hmsf; subst huniq
  exact ⟨by simpa [← hlen] using hbase, hlen.symm, by simpa using hholds⟩

example :
    let s := Memory.State.init ([0, 0, 1, 1] ++ encodeIndexedEdges hRem4)
    let d : SolveHRemArgs := ⟨2, 5, 3, 1⟩
    let res := (Memory.spec 0).clientResult s (pr02SolveHRemProg d)
    let s' := (Memory.spec 0).clientState s (pr02SolveHRemProg d)
    pr02SolveHRemProgSafe 16 d s ∧ res.numEdges = 1 ∧ res.edgeBase + 4 ≤ s'.frontier ∧
    readIndexedEdges res.edgeBase 1 s'.mem = [(1, 3, 4, 102)] ∧ ∀ a < 17, s'.mem a = s.mem a := by
  intro s d res s'
  have hwf : Memory.WellFormed 16 s := Memory.wellFormed_init (by decide) (by decide)
  obtain ⟨hsafe, _, hft⟩ := rounds4_hrem_cert (hRemBase := 5) (conglomBase := 1) hwf
    (hRem4_holds_of_eq (by dsimp only [s]; decide)) (by decide) (by decide)
    (fun u => by dsimp only [s]; fin_cases u <;> decide) (by decide)
  obtain ⟨_, _, hmod, hbase, hlen, hholds⟩ := framedTriple_iff_realization.mp hft
  obtain ⟨h00, h01, h02, h03⟩ := hholds 0 (by decide)
  refine ⟨hsafe, hlen, hbase, ?_,
    fun a ha => hmod.mem_eq_of_not_mem (by change a < 17; omega) (Set.notMem_empty a)⟩
  simp only [readIndexedEdges, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
    List.map_nil]; rw [h00, h01, h02, h03]; rfl

/-! ## 4. Composite `realize [...]` Pipeline and `Program .standard` Lowering -/

private def partEvalPipelineProg (p : EvalDTLoopArgs × SolveHRemArgs) : Memory.Prog ℕ := do
  let fcLen ← pr02EvalDTLoop p.1; let remRes ← pr02SolveHRemProg p.2; pure (fcLen + remRes.numEdges)

private theorem realizes_partEvalPipelineProg : Realizes .exact
    partEvalPipelineProg WordEncoding.encode (WordEncoding.encode (α := ℕ))
    (fun w p s => Fits w 16 ∧ pr02EvalDTLoopSafe w p.1 s ∧
      let s1 := (Memory.spec 0).clientState s (pr02EvalDTLoop p.1)
      let fcLen := (Memory.spec 0).clientResult s (pr02EvalDTLoop p.1)
      let remRes := (Memory.spec 0).clientResult s1 (pr02SolveHRemProg p.2)
      pr02SolveHRemProgSafe w p.2 s1 ∧ Fits w (fcLen + remRes.numEdges))
    (fun _ _ => 0) := by
  unfold partEvalPipelineProg; realize [realizes_pr02EvalDTLoop, realizes_pr02SolveHRemProg]
  all_goals obtain ⟨h16, h1, h2, hsum⟩ := h; first | exact h1 | exact h2 | exact hsum

private def stdEnv4 : EvalDTLoopArgs := ⟨2, 10, 31, 37, 39⟩
private def stdRem4 : SolveHRemArgs := ⟨2, 59, 3, 55⟩
private def stdWords4 : List ℕ :=
  [2, 10, 31, 37, 39, 2, 59, 3, 55] ++ evalLoopBlock4 10 ++ [0, 0, 1, 1] ++ encodeIndexedEdges hRem4

example :
    ∃ r C pc : ℕ, ∃ prog : Program .standard r, ¬prog.ReadsWidth ∧ prog.IsRandFree ∧
      ∃ frontier : Fin r, ∃ y n, Runs 16 prog (State.init stdWords4) ⟨pc, y⟩ n ∧
        step 16 prog ⟨pc, y⟩ = .halt 3 ∧
        memoryState frontier y = (Memory.spec 16).clientState (Memory.State.init stdWords4)
          (partEvalPipelineProg (stdEnv4, stdRem4)) ∧
        n + 1 ≤ C * (memoryCost (partEvalPipelineProg (stdEnv4, stdRem4))
          (Memory.State.init stdWords4) + 1) + 1 := by
  obtain ⟨r, C, pc, prog, hnw, frontier, _, hrun⟩ :=
    realizes_partEvalPipelineProg.exists_standard_basis_init_program_state_from_words (0 : Fin 1)
  have hlayout : ∀ j : Fin 9, stdWords4.getD j.val 0 = WordEncoding.encode (stdEnv4, stdRem4) j :=
    fun j => by fin_cases j <;> rfl
  let s0 := Memory.State.init stdWords4; have hs0_fr : s0.frontier = 71 := rfl
  have hwf0 : Memory.WellFormed 16 s0 := Memory.wellFormed_init (by decide) (by decide)
  obtain ⟨hsafe1, hft1⟩ := rounds4_eval_cert (tBase := 10) hwf0 (by rw [hs0_fr]; decide)
    (by rw [hs0_fr]; decide) (by dsimp only [s0]; decide)
  change pr02EvalDTLoopSafe 16 stdEnv4 s0 at hsafe1
  change Memory.FramedTriple 16 s0 (pr02EvalDTLoop stdEnv4) _ (Set.Ico 39 55) _ at hft1
  let s1 := (Memory.spec 0).clientState s0 (pr02EvalDTLoop stdEnv4)
  obtain ⟨hvh1, _, hmod1, hfc_eq, hs0_s1, hs1_fr, hwf1, _⟩ := framedTriple_iff_realization.mp hft1
  change s0.frontier ≤ s1.frontier at hs0_s1; change s1.frontier ≤ s0.frontier + 42 at hs1_fr
  have hpres : ∀ a, 55 ≤ a → a < 71 → s1.mem a = s0.mem a := fun a ha1 ha2 =>
    hmod1.mem_eq_of_not_mem (by rw [hs0_fr]; exact ha2) (by simp only [Set.mem_Ico]; omega)
  have hrem1 : HoldsIndexedEdges 59 hRem4 s1.mem := hRem4_holds_of_eq (by
    rw [List.map_congr_left fun i hi => hpres _ (by simp at hi; omega) (by simp at hi; omega)]
    dsimp only [s0]; decide)
  have hcong1 : ∀ u : Fin 4, s1.mem (55 + u.val) = (conglomFn4 u).val := fun u => by
    rw [hpres _ (by omega) (by have := u.isLt; omega)]; dsimp only [s0]; fin_cases u <;> decide
  obtain ⟨hsafe2, _, hft2⟩ := rounds4_hrem_cert (hRemBase := 59) (conglomBase := 55) (s := s1)
    hwf1 hrem1 (by rw [hs0_fr] at hs0_s1; omega) (by rw [hs0_fr] at hs0_s1; omega) hcong1
    (Fits.of_le (by decide : Fits 16 7255) (by rw [hs0_fr] at hs1_fr; omega))
  change pr02SolveHRemProgSafe 16 stdRem4 s1 at hsafe2
  change Memory.FramedTriple 16 s1 (pr02SolveHRemProg stdRem4) _ ∅ _ at hft2
  obtain ⟨hvh2, _, _, _, hrem_len, _⟩ := framedTriple_iff_realization.mp hft2
  have hv_all : (Memory.spec 16).ValidHistory s0
      ((Memory.spec 16).clientHistory s0 (partEvalPipelineProg (stdEnv4, stdRem4))) := by
    dsimp only [partEvalPipelineProg]; rw [validHistory_bind']; refine ⟨hvh1, ?_⟩
    change (Memory.spec 16).ValidHistory s1
      ((Memory.spec 16).clientHistory s1 (pr02SolveHRemProg stdRem4 >>= fun remRes =>
        pure ((Memory.spec 0).clientResult s0 (pr02EvalDTLoop stdEnv4) + remRes.numEdges)))
    rw [validHistory_bind']; exact ⟨hvh2, trivial⟩
  have hres_all :
      (Memory.spec 16).clientResult s0 (partEvalPipelineProg (stdEnv4, stdRem4)) = 3 := by
    rw [clientResult_width 16]; dsimp only [partEvalPipelineProg]
    rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_bind,
      StateTransitionSpec.clientResult_pure, hfc_eq]; simpa [s1] using congrArg (2 + ·) hrem_len
  have hpre : Fits 16 16 ∧ pr02EvalDTLoopSafe 16 stdEnv4 s0 ∧ pr02SolveHRemProgSafe 16 stdRem4 s1 ∧
      Fits 16 ((Memory.spec 0).clientResult s0 (pr02EvalDTLoop stdEnv4) +
        ((Memory.spec 0).clientResult s1 (pr02SolveHRemProg stdRem4)).numEdges) :=
    ⟨by decide, hsafe1, hsafe2, by rw [hfc_eq, hrem_len]; decide⟩
  obtain ⟨y, n, hruns, hhalt, hmem_eq, _, hsteps⟩ := hrun 16 (stdEnv4, stdRem4) stdWords4 hlayout
    (by decide) (by decide) (by decide) hpre hv_all
  exact ⟨r, C, pc, stripRand prog, not_readsWidth_stripRand hnw, isRandFree_stripRand prog,
    frontier, y, n, runs_stripRand hruns, step_stripRand_of_halt (hres_all ▸ hhalt), hmem_eq,
    hsteps⟩

end CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.OptimalMSFPartitionEval
