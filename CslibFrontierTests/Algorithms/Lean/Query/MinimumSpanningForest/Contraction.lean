/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.Contraction
public import CslibFrontier.Algorithms.Lean.Kruskal.Basic
import Mathlib.Tactic.FinCases

/-!
# Client Tests for `Query.MinimumSpanningForest.Contraction`

Kernel-checked tests for `Cslib.Query.MinimumSpanningForest` (`Threshold` and `Robust`) covering:
- Tier 1 (happy paths): threshold-rank partition equivalence
  (`isMinSpanningForest_iff_threshold_partition`, `msfEdges_isSpanningForest`,
  `msfEdges_threshold_partition`), cut-step extension and contraction lifting
  (`exists_extend_isMinSpanningForest_of_cutStep`, `isMinSpanningForest_append_of_contract`),
  weak-support pruning (`isMinSpanningForest_of_weakSupport`), `DynamicDJPTree` +
  `DynamicDJPTree.rel_treeEdges_filter_of_border` + `weaklySupported_of_dynamicDJPTree` +
  `isMinSpanningForest_of_dynamicDJPTree`, conglomerate stopping rule
  (`maxsize_le_card_biUnion_of_stop`), and `dedupSimpleEdges` + `edgeEnds` + `edgeWeight` +
  `Cslib.Multigraph.msf`.
- Tier 2 (boundary cases): empty edge lists (`n = 0`, `n = 4`), 1-vertex self-loops,
  disconnected forest with isolated vertex, all-equal weights (`W = 0`, `W = 7`) and tie-breaking,
  duplicate/reversed/self-loop deduplication, and corrupted border edge `M_C` in
  `weaklySupported_of_dynamicDJPTree`.
- Tier 3 (cross-feature): `Kruskal.kruskalEdges` oracle cross-checks.
-/

public section

namespace CslibFrontierTests.Algorithms.Lean.Query.MinimumSpanningForest.Contraction

open Cslib Cslib.Query
open Cslib.DataStructure.DisjointSet
open Cslib.Algorithms.Lean.Kruskal
open Cslib.Query.MinimumSpanningForest

instance decidableWeaklySupported {n : ℕ} (G_b : List (WeightedEdge n ℕ))
    (e : WeightedEdge n ℕ) : Decidable (WeaklySupported G_b e) :=
  inferInstanceAs (Decidable
    ((edgePartition (G_b.filter fun f => decide (f.weight ≤ e.weight))).rel e.u e.v = true))

/-! ### Tier 1: Happy-Path Equivalence Classes -/

/-- T1.1: Threshold-rank partition equivalence on `diamond` (`n = 4, m = 5`). -/
@[expose] def diamondEs : List (WeightedEdge 4 ℕ) :=
  [⟨0, 3, 9⟩, ⟨0, 1, 1⟩, ⟨1, 2, 4⟩, ⟨0, 2, 3⟩, ⟨2, 3, 2⟩]

@[expose] def diamondF : List (WeightedEdge 4 ℕ) :=
  [⟨0, 1, 1⟩, ⟨2, 3, 2⟩, ⟨0, 2, 3⟩]

example :
    edgePartition (diamondF.filter fun e => decide (e.weight ≤ 2)) =
      edgePartition (diamondEs.filter fun e => decide (e.weight ≤ 2)) ∧
      edgePartition (diamondF.filter fun e => decide (e.weight ≤ 4)) =
        edgePartition (diamondEs.filter fun e => decide (e.weight ≤ 4)) := by
  decide

example :
    IsMinSpanningForest diamondEs diamondF ∧
      (∀ t : ℕ,
        edgePartition (diamondF.filter fun e => decide (e.weight ≤ t)) =
          edgePartition (diamondEs.filter fun e => decide (e.weight ≤ t))) ∧
      (∃ F_ext : List (WeightedEdge 4 ℕ),
        IsMinSpanningForest diamondEs (⟨0, 1, 1⟩ :: F_ext)) ∧
      IsMinSpanningForest diamondEs ([⟨0, 1, 1⟩] ++ [⟨2, 3, 2⟩, ⟨0, 2, 3⟩]) := by
  have hk : kruskalEdges diamondEs = diamondF := by
    rw [kruskalEdges, show sortEdges diamondEs =
      [⟨0, 1, 1⟩, ⟨2, 3, 2⟩, ⟨0, 2, 3⟩, ⟨1, 2, 4⟩, ⟨0, 3, 9⟩] by
        simp [diamondEs, sortEdges_cons_cons]]
    rfl
  have hF : IsMinSpanningForest diamondEs diamondF :=
    hk ▸ kruskalEdges_isMinSpanningForest diamondEs
  have hmin : ∀ f ∈ diamondEs,
      (f.u ∈ ({0} : Finset (Fin 4)) ↔ f.v ∉ ({0} : Finset (Fin 4))) → 1 ≤ f.weight := by
    intro f hf _
    simp only [diamondEs, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl <;> decide
  have hext := exists_extend_isMinSpanningForest_of_cutStep diamondEs ⟨0, 1, 1⟩
    (by decide) {0} (by decide) hmin
  let c : Fin 4 → Fin 3
    | 0 => 0
    | 1 => 0
    | 2 => 1
    | 3 => 2
  have hF'_sub : ([⟨0, 1, 1⟩] : List (WeightedEdge 4 ℕ)).Subperm diamondEs :=
    (show ([⟨0, 1, 1⟩] : List (WeightedEdge 4 ℕ)).Sublist diamondEs by decide).subperm
  have hc : ∀ x y : Fin 4,
      c x = c y ↔ (edgePartition ([⟨0, 1, 1⟩] : List (WeightedEdge 4 ℕ))).rel x y = true := by
    intro x y; fin_cases x <;> fin_cases y <;> decide
  have hsurj : Function.Surjective c := fun y => by
    fin_cases y
    · exact ⟨0, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  have hL_sub : ([⟨2, 3, 2⟩, ⟨0, 2, 3⟩] : List (WeightedEdge 4 ℕ)).Subperm diamondEs :=
    (List.Perm.swap (⟨0, 2, 3⟩ : WeightedEdge 4 ℕ) ⟨2, 3, 2⟩ []).subperm.trans
      (show ([⟨0, 2, 3⟩, ⟨2, 3, 2⟩] : List (WeightedEdge 4 ℕ)).Sublist diamondEs by
        decide).subperm
  have hkC : kruskalEdges (contractEdgeList c diamondEs) =
      contractEdgeList c [⟨2, 3, 2⟩, ⟨0, 2, 3⟩] := by
    rw [kruskalEdges, show sortEdges (contractEdgeList c diamondEs) =
      [⟨0, 0, 1⟩, ⟨1, 2, 2⟩, ⟨0, 1, 3⟩, ⟨0, 1, 4⟩, ⟨0, 2, 9⟩] by
        simp [contractEdgeList, contractEdge, c, diamondEs, sortEdges_cons_cons]]
    rfl
  have hL_msf : IsMinSpanningForest (contractEdgeList c diamondEs)
      (contractEdgeList c [⟨2, 3, 2⟩, ⟨0, 2, 3⟩]) :=
    hkC ▸ kruskalEdges_isMinSpanningForest _
  have hext' : ∃ F_ext, IsMinSpanningForest diamondEs ([⟨0, 1, 1⟩] ++ F_ext) :=
    let ⟨F_ext, h⟩ := hext; ⟨F_ext, h⟩
  exact ⟨hF, (isMinSpanningForest_iff_threshold_partition diamondEs diamondF).mp hF |>.2, hext,
    isMinSpanningForest_append_of_contract diamondEs [⟨0, 1, 1⟩] [⟨2, 3, 2⟩, ⟨0, 2, 3⟩] c
      hF'_sub (by decide) hc hsurj hext' hL_sub hL_msf⟩

/-- T1.2: Weakly supported pruning (`isMinSpanningForest_of_weakSupport`). -/
@[expose] def pathChordG : List (WeightedEdge 4 ℕ) :=
  [⟨0, 1, 2⟩, ⟨1, 2, 3⟩, ⟨2, 3, 4⟩, ⟨0, 3, 10⟩, ⟨0, 2, 5⟩]

@[expose] def pathChordGb : List (WeightedEdge 4 ℕ) :=
  [⟨0, 1, 2⟩, ⟨1, 2, 3⟩, ⟨2, 3, 4⟩]

example : pathChordG.all (fun e => decide (WeaklySupported pathChordGb e)) = true := by decide

example : IsMinSpanningForest pathChordG pathChordGb := by
  have hsub : pathChordGb.Subperm pathChordG :=
    (show pathChordGb.Sublist pathChordG by decide).subperm
  have hws : ∀ e ∈ pathChordG, WeaklySupported pathChordGb e := by
    intro e he
    simp only [pathChordG, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl <;> decide
  have hk : kruskalEdges pathChordGb = pathChordGb := by
    rw [kruskalEdges, show sortEdges pathChordGb = pathChordGb by
      simp [pathChordGb, sortEdges_cons_cons]]
    rfl
  have hFb : IsMinSpanningForest pathChordGb pathChordGb := by
    have h := kruskalEdges_isMinSpanningForest pathChordGb
    rwa [hk] at h
  exact isMinSpanningForest_of_weakSupport pathChordG pathChordGb pathChordGb hsub hws hFb

/-- T1.3: `DynamicDJPTree` + `rel_treeEdges_filter_of_border` +
`weaklySupported_of_dynamicDJPTree` (`n = 5`). -/
@[expose] def djpTree5 : DynamicDJPTree 5 where
  numSteps := 2
  root := 0
  edge
    | 0 => ⟨0, 1, 2⟩
    | 1 => ⟨1, 2, 4⟩
  wPop
    | 0 => 3
    | 1 => 4
  vIn
    | 0 => 0
    | 1 => 1
  vOut
    | 0 => 1
    | 1 => 2
  edge_weight_le_wPop s := by fin_cases s <;> decide
  ends_match s := by fin_cases s <;> simp
  vIn_mem s := by fin_cases s <;> decide
  vOut_not_mem s := by fin_cases s <;> decide
  djp_future s s' hlt _ := by fin_cases s <;> fin_cases s' <;> simp_all

@[expose] def djpC : List (WeightedEdge 5 ℕ) := [⟨0, 1, 2⟩, ⟨1, 2, 4⟩, ⟨0, 2, 6⟩]
@[expose] def djpH : List (WeightedEdge 5 ℕ) := [⟨2, 3, 5⟩, ⟨0, 3, 8⟩, ⟨3, 4, 7⟩]
@[expose] def djpEs : List (WeightedEdge 5 ℕ) := djpC ++ [] ++ djpH
@[expose] def djpFC : List (WeightedEdge 5 ℕ) := [⟨0, 1, 2⟩, ⟨1, 2, 4⟩]
@[expose] def djpHLift : List (WeightedEdge 5 ℕ) := [⟨2, 3, 5⟩, ⟨3, 4, 7⟩]

@[expose] def djpContract (x : Fin 5) : Fin 3 :=
  match x.val with
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 1
  | _ => 2

example :
    djpTree5.treeEdges = [⟨0, 1, 2⟩, ⟨1, 2, 4⟩] ∧
      contractEdgeList djpContract djpH = [⟨0, 1, 5⟩, ⟨0, 1, 8⟩, ⟨1, 2, 7⟩] := by
  decide

example :
    (edgePartition (djpTree5.treeEdges.filter fun e =>
      decide (e.weight ≤ max 5 8))).rel 0 2 = true ∧
      Cslib.Multigraph.Joins djpTree5.ends Set.univ djpTree5.root 2 ∧
      (∀ e ∈ djpEs, WeaklySupported (djpFC ++ djpHLift ++ []) e) ∧
      IsMinSpanningForest djpEs (djpFC ++ djpHLift) := by
  have hVC : djpTree5.treeVerts djpTree5.numSteps = ({0, 1, 2} : Finset (Fin 5)) := by decide
  have h21 := djpTree5.rel_treeEdges_filter_of_border (x := 0) (y := 2) (by decide) (by decide)
    ⟨0, 3, 8⟩ ⟨2, 3, 5⟩ (.inl ⟨rfl, by decide⟩) (.inl ⟨rfl, by decide⟩)
    (fun s _ => by fin_cases s <;> decide) (fun s _ => by fin_cases s <;> decide)
  have hj := djpTree5.joins_treeVerts (x := 2) (by decide)
  have hDsub : djpTree5.treeEdges.Subperm djpC :=
    (show djpTree5.treeEdges.Sublist djpC by decide).subperm
  have hHno : ∀ e ∈ djpH,
      ¬ (e.u ∈ djpTree5.treeVerts djpTree5.numSteps ∧
        e.v ∈ djpTree5.treeVerts djpTree5.numSteps) := by
    rw [hVC]
    intro e he
    simp only [djpH, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;> decide
  have huncorr : ∀ e ∈ djpH, ∀ s : Fin djpTree5.numSteps,
      (e.u ∈ djpTree5.treeVerts s.val ↔ e.v ∉ djpTree5.treeVerts s.val) →
      djpTree5.wPop s ≤ e.weight := by
    intro e he s _
    simp only [djpH, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;> fin_cases s <;> decide
  have hc : ∀ x y : Fin 5, djpContract x = djpContract y ↔
      x = y ∨ (x ∈ djpTree5.treeVerts djpTree5.numSteps ∧
        y ∈ djpTree5.treeVerts djpTree5.numSteps) := by
    rw [hVC]
    intro x y; fin_cases x <;> fin_cases y <;> decide
  have hkC : kruskalEdges djpC = djpFC := by
    rw [kruskalEdges, show sortEdges djpC = djpC by simp [djpC, sortEdges_cons_cons]]
    rfl
  have hFC : IsMinSpanningForest djpC djpFC := hkC ▸ kruskalEdges_isMinSpanningForest djpC
  have hHLsub : djpHLift.Subperm djpH :=
    (show djpHLift.Sublist djpH by decide).subperm
  have hkHL : kruskalEdges (contractEdgeList djpContract djpH) =
      contractEdgeList djpContract djpHLift := by
    rw [kruskalEdges, show sortEdges (contractEdgeList djpContract djpH) =
      [⟨0, 1, 5⟩, ⟨1, 2, 7⟩, ⟨0, 1, 8⟩] by
        simp [contractEdgeList, contractEdge, djpContract, djpH, sortEdges_cons_cons]]
    rfl
  have hHLmsf : IsMinSpanningForest (contractEdgeList djpContract djpH)
      (contractEdgeList djpContract djpHLift) :=
    hkHL ▸ kruskalEdges_isMinSpanningForest _
  have hkF : kruskalEdges (djpFC ++ djpHLift ++ []) = djpFC ++ djpHLift := by
    rw [kruskalEdges, show sortEdges (djpFC ++ djpHLift ++ []) =
      [⟨0, 1, 2⟩, ⟨1, 2, 4⟩, ⟨2, 3, 5⟩, ⟨3, 4, 7⟩] by
        simp [djpFC, djpHLift, sortEdges_cons_cons]]
    rfl
  have hF : IsMinSpanningForest (djpFC ++ djpHLift ++ []) (djpFC ++ djpHLift) := by
    have h := kruskalEdges_isMinSpanningForest (djpFC ++ djpHLift ++ [])
    rwa [hkF] at h
  exact ⟨h21, hj,
    weaklySupported_of_dynamicDJPTree djpEs djpC [] djpH djpFC djpHLift djpTree5 djpContract
      List.Perm.rfl hDsub hHno huncorr hc hFC hHLsub hHLmsf,
    isMinSpanningForest_of_dynamicDJPTree djpEs djpC [] djpH djpFC djpHLift (djpFC ++ djpHLift)
      djpTree5 djpContract List.Perm.rfl hDsub hHno huncorr hc hFC hHLsub hHLmsf hF⟩

/-- T1.4: `maxsize_le_card_biUnion_of_stop` conglomerate size lower bound. -/
@[expose] def roundVComp : Fin 2 → Finset (Fin 5)
  | 0 => {0, 1, 2}
  | 1 => {2, 3}

example :
    2 ≤ (({0, 1} : Finset (Fin 2)).biUnion roundVComp).card ∨
      (({0, 1} : Finset (Fin 2)).card = 1 ∧ ∃ i₀ ∈ ({0, 1} : Finset (Fin 2)),
        ¬ ∃ j : Fin 2, j ≠ i₀ ∧ (roundVComp i₀ ∩ roundVComp j).Nonempty) := by
  have hstop : ∀ i : Fin 2,
      2 ≤ (roundVComp i).card ∨
      (∃ j : Fin 2, j.val < i.val ∧ (roundVComp i ∩ roundVComp j).Nonempty) ∨
      ¬ ∃ i' : Fin 2, i' ≠ i ∧ (roundVComp i ∩ roundVComp i').Nonempty := by
    intro i; fin_cases i
    · left; decide
    · right; left
      exact ⟨0, by decide, ⟨2, Finset.mem_inter.mpr ⟨by decide, by decide⟩⟩⟩
  have hclosed : ∀ i ∈ ({0, 1} : Finset (Fin 2)), ∀ j : Fin 2,
      (roundVComp i ∩ roundVComp j).Nonempty → j ∈ ({0, 1} : Finset (Fin 2)) := by
    intro i _ j _; fin_cases j <;> decide
  have hconn : ∀ J : Finset (Fin 2), J.Nonempty → J ⊂ ({0, 1} : Finset (Fin 2)) →
      ∃ a ∈ J, ∃ b ∈ ({0, 1} : Finset (Fin 2)) \ J,
        (roundVComp a ∩ roundVComp b).Nonempty := by
    intro J hJne hJss
    fin_cases J
    · simp at hJne
    · exact ⟨0, by decide, 1, by decide, ⟨2, Finset.mem_inter.mpr ⟨by decide, by decide⟩⟩⟩
    · exact ⟨1, by decide, 0, by decide, ⟨2, Finset.mem_inter.mpr ⟨by decide, by decide⟩⟩⟩
    · exact absurd hJss (lt_irrefl _)
  exact maxsize_le_card_biUnion_of_stop roundVComp hstop {0, 1} (by decide) hclosed hconn

/-- T1.5: `dedupSimpleEdges`, `edgeEnds`, `edgeWeight`, and `Cslib.Multigraph.msf` lifting. -/
@[expose] def multiTriEs : List (WeightedEdge 3 ℕ) :=
  [⟨0, 1, 8⟩, ⟨1, 0, 3⟩, ⟨1, 2, 5⟩, ⟨0, 2, 7⟩, ⟨2, 0, 4⟩]

abbrev multiTriDedup : List (WeightedEdge 3 ℕ) :=
  [⟨1, 0, 3⟩, ⟨2, 0, 4⟩, ⟨1, 2, 5⟩]

example : dedupSimpleEdges multiTriEs = multiTriDedup := by decide

example :
    IsSimple (edgeEnds (dedupSimpleEdges multiTriEs)) ∧
      edgeWeight multiTriEs ⟨1, by decide⟩ < edgeWeight multiTriEs ⟨0, by decide⟩ ∧
      Cslib.Multigraph.msf (edgeEnds multiTriDedup) (edgeWeight multiTriDedup)
        Finset.univ = {0, 1} ∧
      IsMinSpanningForest multiTriEs [⟨1, 0, 3⟩, ⟨2, 0, 4⟩] := by
  have hd : dedupSimpleEdges multiTriEs = multiTriDedup := by decide
  have hk : kruskalEdges (dedupSimpleEdges multiTriEs) = [⟨1, 0, 3⟩, ⟨2, 0, 4⟩] := by
    rw [hd, kruskalEdges, show sortEdges multiTriDedup = multiTriDedup by
      simp [multiTriDedup, sortEdges_cons_cons]]
    rfl
  have hF : IsMinSpanningForest (dedupSimpleEdges multiTriEs) [⟨1, 0, 3⟩, ⟨2, 0, 4⟩] :=
    hk ▸ kruskalEdges_isMinSpanningForest _
  have hlt : edgeWeight multiTriEs ⟨1, by decide⟩ < edgeWeight multiTriEs ⟨0, by decide⟩ :=
    Prod.Lex.lt_iff.mpr (.inl (by decide))
  have hmsf : Cslib.Multigraph.msf (edgeEnds multiTriDedup) (edgeWeight multiTriDedup)
      Finset.univ = {0, 1} := by
    ext e
    rw [Finset.mem_insert, Finset.mem_singleton]
    induction he : edgeEnds multiTriDedup e using Sym2.ind with
    | _ a b =>
      rw [Cslib.Multigraph.mem_msf_iff (edgeWeight multiTriDedup) he]
      fin_cases e <;> dsimp only
      · refine ⟨fun _ => Or.inl rfl, fun _ => ⟨Finset.mem_univ _, fun hj => ?_⟩⟩
        have hsub0 : ∀ f ∈ {f : Fin 3 | f ∈ (Finset.univ : Finset (Fin 3)) ∧
            edgeWeight multiTriDedup f < edgeWeight multiTriDedup ⟨0, by decide⟩}, False := by
          intro f hf
          have h := hf.2
          fin_cases f <;>
            simp only [multiTriDedup, edgeWeight, Prod.Lex.lt_iff, ofLex_toLex] at h <;>
            (revert h; decide)
        have hne : a ≠ b := by
          intro h; subst h
          have hs : (s(1, 0) : Sym2 (Fin 3)) = s(a, a) := he
          rw [Sym2.eq_iff] at hs; rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
        obtain ⟨f, hf, _⟩ := hj.exists_mem_edgeCut (P := {x : Fin 3 | x = a}) rfl hne.symm
        exact hsub0 f hf
      · refine ⟨fun _ => Or.inr rfl, fun _ => ⟨Finset.mem_univ _, fun hj => ?_⟩⟩
        have hsub : ∀ f ∈ {f : Fin 3 | f ∈ (Finset.univ : Finset (Fin 3)) ∧
            edgeWeight multiTriDedup f < edgeWeight multiTriDedup ⟨1, by decide⟩}, f = 0 := by
          intro f hf
          have hlt1 := hf.2
          fin_cases f
          · rfl
          · exfalso
            simp only [multiTriDedup, edgeWeight, Prod.Lex.lt_iff, ofLex_toLex] at hlt1
            revert hlt1; decide
          · exfalso
            simp only [multiTriDedup, edgeWeight, Prod.Lex.lt_iff, ofLex_toLex] at hlt1
            revert hlt1; decide
        have ha_eq : (a = 2 ∧ b = 0) ∨ (a = 0 ∧ b = 2) := Sym2.eq_iff.mp he.symm
        rcases ha_eq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · obtain ⟨f, hf, hcut⟩ := hj.exists_mem_edgeCut (P := {x : Fin 3 | x = 2}) rfl (by decide)
          obtain ⟨u, v, huv, hu, hv⟩ := Graph.mem_edgeCut_iff.1 hcut
          have r0 := hsub f hf; subst r0
          have hs : (s(1, 0) : Sym2 (Fin 3)) = s(u, v) := huv
          rcases Sym2.eq_iff.mp hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp at hu hv
        · obtain ⟨f, hf, hcut⟩ :=
            hj.exists_mem_edgeCut (P := {x : Fin 3 | x ≠ 2}) (by decide) (by decide)
          obtain ⟨u, v, huv, hu, hv⟩ := Graph.mem_edgeCut_iff.1 hcut
          have r0 := hsub f hf; subst r0
          have hs : (s(1, 0) : Sym2 (Fin 3)) = s(u, v) := huv
          rcases Sym2.eq_iff.mp hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp at hu hv
      · refine ⟨fun h => False.elim (h.2 ?_), fun h => by rcases h with h | h <;> cases h⟩
        have h0 : (0 : Fin 3) ∈ {f : Fin 3 | f ∈ (Finset.univ : Finset (Fin 3)) ∧
            edgeWeight multiTriDedup f < edgeWeight multiTriDedup 2} :=
          ⟨Finset.mem_univ _, Prod.Lex.lt_iff.mpr (.inl (by decide))⟩
        have h1 : (1 : Fin 3) ∈ {f : Fin 3 | f ∈ (Finset.univ : Finset (Fin 3)) ∧
            edgeWeight multiTriDedup f < edgeWeight multiTriDedup 2} :=
          ⟨Finset.mem_univ _, Prod.Lex.lt_iff.mpr (.inl (by decide))⟩
        have j0 := Cslib.Multigraph.Joins.of_mem h0 (show edgeEnds multiTriDedup 0 = s(1, 0) by rfl)
        have j1 := Cslib.Multigraph.Joins.of_mem h1 (show edgeEnds multiTriDedup 1 = s(2, 0) by rfl)
        rcases Sym2.eq_iff.mp he.symm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact j0.trans j1.symm
        · exact j1.trans j0.symm
  exact ⟨dedupSimpleEdges_isSimple multiTriEs, hlt, hmsf,
    isMinSpanningForest_of_dedupSimpleEdges multiTriEs [⟨1, 0, 3⟩, ⟨2, 0, 4⟩] hF⟩

/-! ### Tier 2: Boundary and Corner Cases -/

/-- T2.1: Empty edge lists (`n = 0` and `n = 4`). -/
@[expose] def empty0Es : List (WeightedEdge 0 ℕ) := []
@[expose] def empty4Es : List (WeightedEdge 4 ℕ) := []

example :
    dedupSimpleEdges empty4Es = [] ∧
      contractEdgeList (fun _ : Fin 4 => (0 : Fin 1)) empty4Es = [] := by
  decide

example :
    IsSimple (edgeEnds (dedupSimpleEdges empty0Es)) ∧
      IsMinSpanningForest empty4Es [] ∧
      ∀ t : ℕ,
        edgePartition (([] : List (WeightedEdge 4 ℕ)).filter fun e => decide (e.weight ≤ t)) =
          edgePartition (empty4Es.filter fun e => decide (e.weight ≤ t)) := by
  have hd : dedupSimpleEdges empty4Es = [] := by decide
  have hk : kruskalEdges (dedupSimpleEdges empty4Es) = [] := by
    rw [hd, kruskalEdges, sortEdges_nil]; rfl
  have hF : IsMinSpanningForest empty4Es [] :=
    isMinSpanningForest_of_dedupSimpleEdges empty4Es []
      (hk ▸ kruskalEdges_isMinSpanningForest (dedupSimpleEdges empty4Es))
  exact ⟨dedupSimpleEdges_isSimple empty0Es, hF,
    (isMinSpanningForest_iff_threshold_partition empty4Es []).mp hF |>.2⟩

/-- T2.2: 1-vertex graph with self-loops (`n = 1`). -/
@[expose] def loop1Es : List (WeightedEdge 1 ℕ) := [⟨0, 0, 0⟩, ⟨0, 0, 5⟩]

example :
    dedupSimpleEdges loop1Es = [] ∧
      WeaklySupported ([] : List (WeightedEdge 1 ℕ)) ⟨0, 0, 0⟩ := by
  decide

example :
    IsSimple (edgeEnds (dedupSimpleEdges loop1Es)) ∧
      IsMinSpanningForest loop1Es [] := by
  have hd : dedupSimpleEdges loop1Es = [] := by decide
  have hk : kruskalEdges (dedupSimpleEdges loop1Es) = [] := by
    rw [hd, kruskalEdges, sortEdges_nil]; rfl
  exact ⟨dedupSimpleEdges_isSimple loop1Es,
    isMinSpanningForest_of_dedupSimpleEdges loop1Es []
      (hk ▸ kruskalEdges_isMinSpanningForest (dedupSimpleEdges loop1Es))⟩

/-- T2.3: Disconnected forest with isolated vertex (`n = 5`, components `{0,1}`, `{2,3}`, `4`). -/
@[expose] def disc5Es : List (WeightedEdge 5 ℕ) :=
  [⟨0, 1, 6⟩, ⟨1, 0, 2⟩, ⟨2, 3, 4⟩, ⟨3, 2, 9⟩]

example :
    dedupSimpleEdges disc5Es = [⟨1, 0, 2⟩, ⟨2, 3, 4⟩] ∧
      (edgePartition disc5Es).numComponents = 3 := by
  decide

example : IsMinSpanningForest disc5Es [⟨1, 0, 2⟩, ⟨2, 3, 4⟩] := by
  have hd : dedupSimpleEdges disc5Es = [⟨1, 0, 2⟩, ⟨2, 3, 4⟩] := by decide
  have hk : kruskalEdges (dedupSimpleEdges disc5Es) = [⟨1, 0, 2⟩, ⟨2, 3, 4⟩] := by
    rw [hd, kruskalEdges, show sortEdges [⟨1, 0, 2⟩, ⟨2, 3, 4⟩] =
      [⟨1, 0, 2⟩, ⟨2, 3, 4⟩] by simp [sortEdges_cons_cons]]
    rfl
  have hF : IsMinSpanningForest (dedupSimpleEdges disc5Es) [⟨1, 0, 2⟩, ⟨2, 3, 4⟩] :=
    hk ▸ kruskalEdges_isMinSpanningForest _
  exact isMinSpanningForest_of_dedupSimpleEdges disc5Es [⟨1, 0, 2⟩, ⟨2, 3, 4⟩] hF

/-- T2.4: All-equal weights (`W = 0` and `W = 7`), `edgeWeight` tie-breaking, non-unique MSF. -/
@[expose] def eq0Es : List (WeightedEdge 3 ℕ) := [⟨0, 1, 0⟩, ⟨1, 2, 0⟩, ⟨0, 2, 0⟩]
@[expose] def eq7Es : List (WeightedEdge 3 ℕ) := [⟨0, 1, 7⟩, ⟨1, 2, 7⟩, ⟨0, 2, 7⟩]
@[expose] def eq7AltF : List (WeightedEdge 3 ℕ) := [⟨1, 2, 7⟩, ⟨0, 2, 7⟩]

example :
    WeaklySupported eq7AltF ⟨0, 1, 7⟩ := by decide

example :
    edgeWeight eq7Es ⟨0, by decide⟩ < edgeWeight eq7Es ⟨2, by decide⟩ ∧
      IsMinSpanningForest eq7Es eq7AltF := by
  have hsub : eq7AltF.Subperm eq7Es := (show eq7AltF.Sublist eq7Es by decide).subperm
  have hac : IsAcyclic eq7AltF := by decide
  have hpart : edgePartition eq7AltF = edgePartition eq7Es := by decide
  have hthr : ∀ t : ℕ,
      edgePartition (eq7AltF.filter fun e => decide (e.weight ≤ t)) =
        edgePartition (eq7Es.filter fun e => decide (e.weight ≤ t)) := by
    intro t
    by_cases ht : 7 ≤ t
    · have hf1 : eq7AltF.filter (fun e => decide (e.weight ≤ t)) = eq7AltF := by
        simp [eq7AltF, ht]
      have hf2 : eq7Es.filter (fun e => decide (e.weight ≤ t)) = eq7Es := by
        simp [eq7Es, ht]
      rw [hf1, hf2, hpart]
    · have hf1 : eq7AltF.filter (fun e => decide (e.weight ≤ t)) = [] := by
        simp [eq7AltF, ht]
      have hf2 : eq7Es.filter (fun e => decide (e.weight ≤ t)) = [] := by
        simp [eq7Es, ht]
      rw [hf1, hf2]
  exact ⟨Prod.Lex.lt_iff.mpr (.inr ⟨rfl, by decide⟩),
    (isMinSpanningForest_iff_threshold_partition eq7Es eq7AltF).mpr ⟨⟨hsub, hac, hpart⟩, hthr⟩⟩

/-- T2.5: Duplicate identical edges, reversed parallel edges, and zero-weight self-loops. -/
@[expose] def dupLoopsEs : List (WeightedEdge 3 ℕ) :=
  [⟨0, 0, 0⟩, ⟨1, 1, 1⟩, ⟨0, 1, 4⟩, ⟨0, 1, 4⟩, ⟨1, 0, 4⟩, ⟨1, 2, 3⟩, ⟨2, 1, 2⟩]

@[expose] def dupLoopsDedup : List (WeightedEdge 3 ℕ) :=
  [⟨0, 1, 4⟩, ⟨2, 1, 2⟩]

example : dedupSimpleEdges dupLoopsEs = dupLoopsDedup := by decide

example :
    IsSimple (edgeEnds (dedupSimpleEdges dupLoopsEs)) ∧
      IsMinSpanningForest dupLoopsEs [⟨2, 1, 2⟩, ⟨0, 1, 4⟩] ∧
      (edgePartition (dupLoopsEs.filter fun e => decide (e.weight ≤ 4))).rel 0 2 = true := by
  have hsimp := dedupSimpleEdges_isSimple dupLoopsEs
  have hd : dedupSimpleEdges dupLoopsEs = dupLoopsDedup := by decide
  have hk : kruskalEdges (dedupSimpleEdges dupLoopsEs) = [⟨2, 1, 2⟩, ⟨0, 1, 4⟩] := by
    rw [hd, kruskalEdges, show sortEdges dupLoopsDedup =
      [⟨2, 1, 2⟩, ⟨0, 1, 4⟩] by simp [dupLoopsDedup, sortEdges_cons_cons]]
    rfl
  have hF : IsMinSpanningForest (dedupSimpleEdges dupLoopsEs) [⟨2, 1, 2⟩, ⟨0, 1, 4⟩] :=
    hk ▸ kruskalEdges_isMinSpanningForest _
  have hsub : dupLoopsDedup.Subperm dupLoopsEs := hd ▸ dedupSimpleEdges_subperm dupLoopsEs
  have hrel := edgePartition_filter_mono_subperm hsub (t₁ := 4) (t₂ := 4) le_rfl (u := 0) (v := 2)
    (by decide)
  exact ⟨hsimp, isMinSpanningForest_of_dedupSimpleEdges dupLoopsEs [⟨2, 1, 2⟩, ⟨0, 1, 4⟩] hF, hrel⟩

/-- T2.6: Corrupted border edge `M_C` in `weaklySupported_of_dynamicDJPTree`
(`weight < wPop 0`). -/
@[expose] def corrDJP : DynamicDJPTree 3 where
  numSteps := 1
  root := 0
  edge _ := ⟨0, 1, 10⟩
  wPop _ := 10
  vIn _ := 0
  vOut _ := 1
  edge_weight_le_wPop _ := le_rfl
  ends_match _ := .inl ⟨rfl, rfl⟩
  vIn_mem s := by fin_cases s; decide
  vOut_not_mem s := by fin_cases s; decide
  djp_future s s' hlt _ := by fin_cases s; fin_cases s'; exact absurd hlt (Nat.lt_irrefl _)

@[expose] def corrC : List (WeightedEdge 3 ℕ) := [⟨0, 1, 10⟩]
@[expose] def corrMC : List (WeightedEdge 3 ℕ) := [⟨1, 2, 3⟩]
@[expose] def corrH : List (WeightedEdge 3 ℕ) := [⟨0, 2, 12⟩, ⟨1, 2, 15⟩]
@[expose] def corrHLift : List (WeightedEdge 3 ℕ) := [⟨0, 2, 12⟩]
@[expose] def corrEs : List (WeightedEdge 3 ℕ) := corrC ++ corrMC ++ corrH

@[expose] def corrMap (x : Fin 3) : Fin 2 :=
  if x.val ≤ 1 then 0 else 1

example : WeaklySupported (corrC ++ corrHLift ++ corrMC) ⟨1, 2, 15⟩ := by decide

example :
    (∀ e ∈ corrEs, WeaklySupported (corrC ++ corrHLift ++ corrMC) e) ∧
      IsMinSpanningForest corrEs [⟨1, 2, 3⟩, ⟨0, 1, 10⟩] := by
  have hVC : corrDJP.treeVerts corrDJP.numSteps = ({0, 1} : Finset (Fin 3)) := by decide
  have hDsub : corrDJP.treeEdges.Subperm corrC :=
    (show corrDJP.treeEdges.Sublist corrC by decide).subperm
  have hHno : ∀ e ∈ corrH,
      ¬ (e.u ∈ corrDJP.treeVerts corrDJP.numSteps ∧
        e.v ∈ corrDJP.treeVerts corrDJP.numSteps) := by
    rw [hVC]
    intro e he
    simp only [corrH, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> decide
  have huncorr : ∀ e ∈ corrH, ∀ s : Fin corrDJP.numSteps,
      (e.u ∈ corrDJP.treeVerts s.val ↔ e.v ∉ corrDJP.treeVerts s.val) →
      corrDJP.wPop s ≤ e.weight := by
    intro e he s _
    simp only [corrH, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> fin_cases s <;> decide
  have hc : ∀ x y : Fin 3, corrMap x = corrMap y ↔
      x = y ∨ (x ∈ corrDJP.treeVerts corrDJP.numSteps ∧
        y ∈ corrDJP.treeVerts corrDJP.numSteps) := by
    rw [hVC]
    intro x y; fin_cases x <;> fin_cases y <;> decide
  have hkC : kruskalEdges corrC = corrC := by
    rw [kruskalEdges, show sortEdges corrC = corrC by simp [corrC]]
    rfl
  have hFC : IsMinSpanningForest corrC corrC := by
    have h := kruskalEdges_isMinSpanningForest corrC
    rwa [hkC] at h
  have hHLsub : corrHLift.Subperm corrH :=
    (show corrHLift.Sublist corrH by decide).subperm
  have hkHL : kruskalEdges (contractEdgeList corrMap corrH) =
      contractEdgeList corrMap corrHLift := by
    rw [kruskalEdges, show sortEdges (contractEdgeList corrMap corrH) =
      [⟨0, 1, 12⟩, ⟨0, 1, 15⟩] by
        simp [contractEdgeList, contractEdge, corrMap, corrH, sortEdges_cons_cons]]
    rfl
  have hHLmsf : IsMinSpanningForest (contractEdgeList corrMap corrH)
      (contractEdgeList corrMap corrHLift) :=
    hkHL ▸ kruskalEdges_isMinSpanningForest _
  have hkF : kruskalEdges (corrC ++ corrHLift ++ corrMC) = [⟨1, 2, 3⟩, ⟨0, 1, 10⟩] := by
    rw [kruskalEdges, show sortEdges (corrC ++ corrHLift ++ corrMC) =
      [⟨1, 2, 3⟩, ⟨0, 1, 10⟩, ⟨0, 2, 12⟩] by
        simp [corrC, corrHLift, corrMC, sortEdges_cons_cons]]
    rfl
  have hF : IsMinSpanningForest (corrC ++ corrHLift ++ corrMC) [⟨1, 2, 3⟩, ⟨0, 1, 10⟩] :=
    hkF ▸ kruskalEdges_isMinSpanningForest _
  exact ⟨weaklySupported_of_dynamicDJPTree corrEs corrC corrMC corrH corrC corrHLift corrDJP
      corrMap List.Perm.rfl hDsub hHno huncorr hc hFC hHLsub hHLmsf,
    isMinSpanningForest_of_dynamicDJPTree corrEs corrC corrMC corrH corrC corrHLift
      [⟨1, 2, 3⟩, ⟨0, 1, 10⟩] corrDJP corrMap List.Perm.rfl hDsub hHno huncorr hc hFC hHLsub
      hHLmsf hF⟩

/-! ### Tier 3: Cross-Feature Oracle Checks (`kruskalEdges` and `msfEdges`) -/

example :
    kruskalEdges diamondEs = diamondF ∧
      totalWeight (kruskalEdges diamondEs) = 6 ∧
      kruskalEdges eq0Es = [⟨0, 1, 0⟩, ⟨1, 2, 0⟩] ∧
      kruskalEdges eq7Es = [⟨0, 1, 7⟩, ⟨1, 2, 7⟩] ∧
      IsSpanningForest diamondEs (msfEdges diamondEs (edgeWeight diamondEs)) := by
  have hkD : kruskalEdges diamondEs = diamondF := by
    rw [kruskalEdges, show sortEdges diamondEs =
      [⟨0, 1, 1⟩, ⟨2, 3, 2⟩, ⟨0, 2, 3⟩, ⟨1, 2, 4⟩, ⟨0, 3, 9⟩] by
        simp [diamondEs, sortEdges_cons_cons]]
    rfl
  have hk0 : kruskalEdges eq0Es = [⟨0, 1, 0⟩, ⟨1, 2, 0⟩] := by
    rw [kruskalEdges, show sortEdges eq0Es = eq0Es by simp [eq0Es, sortEdges_cons_cons]]
    rfl
  have hk7 : kruskalEdges eq7Es = [⟨0, 1, 7⟩, ⟨1, 2, 7⟩] := by
    rw [kruskalEdges, show sortEdges eq7Es = eq7Es by simp [eq7Es, sortEdges_cons_cons]]
    rfl
  exact ⟨hkD, by rw [hkD]; decide, hk0, hk7,
    msfEdges_isSpanningForest diamondEs (edgeWeight diamondEs) (edgeWeight_injective diamondEs)⟩

-- Step acyclicity, vertex-subset length bound, and injective contraction preservation.
example : IsAcyclic ([(⟨0, 1, 3⟩ : WeightedEdge 3 ℕ), ⟨1, 2, 5⟩]) ∧
    ¬ IsAcyclic ([(⟨0, 2, 7⟩ : WeightedEdge 3 ℕ), ⟨0, 1, 3⟩, ⟨1, 2, 5⟩]) ∧
    [(⟨0, 1, 3⟩ : WeightedEdge 3 ℕ), ⟨1, 2, 5⟩].length ≤
      ({0, 1, 2} : Finset (Fin 3)).card - 1 := by
  have h2 : IsAcyclic ([(⟨0, 1, 3⟩ : WeightedEdge 3 ℕ), ⟨1, 2, 5⟩]) := by decide
  have hnot : ¬ IsAcyclic ([(⟨0, 2, 7⟩ : WeightedEdge 3 ℕ), ⟨0, 1, 3⟩, ⟨1, 2, 5⟩]) := by
    rw [isAcyclic_cons_iff]
    rintro ⟨hrel, _⟩
    have htrue : (edgePartition ([(⟨0, 1, 3⟩ : WeightedEdge 3 ℕ), ⟨1, 2, 5⟩])).rel 0 2 = true := by
      decide
    simp [htrue] at hrel
  have hlen := isAcyclic_length_le_finset_sub_one ({0, 1, 2} : Finset (Fin 3))
    [⟨0, 1, 3⟩, ⟨1, 2, 5⟩] h2 fun e he => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> decide
  exact ⟨h2, hnot, hlen⟩

example : IsAcyclic ([(⟨0, 1, 4⟩ : WeightedEdge 3 ℕ), ⟨1, 2, 9⟩]) := by
  let lift : Fin 3 → Fin 5 := fun k => match k with | 0 => 1 | 1 => 3 | 2 => 4
  have hlift : Function.Injective lift := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [lift]
  have hlifted : IsAcyclic (contractEdgeList lift [⟨0, 1, 4⟩, ⟨1, 2, 9⟩]) := by decide
  exact (isAcyclic_contractEdgeList_iff_of_injective hlift _).mp hlifted

end CslibFrontierTests.Algorithms.Lean.Query.MinimumSpanningForest.Contraction
