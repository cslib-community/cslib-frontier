/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Foundations.Combinatorics.SimpleGraph.MinimumSpanningTree
import CslibFrontier.Algorithms.Lean.Kruskal.SimpleGraph
import CslibFrontier.Computability.Distributed.MinimumSpanningTree.GHS

/-! Checked `module` client tests for `SimpleGraph.IsMST` and
`Cslib.Distributed.MinimumSpanningTree` using ordinary imports:
1. `Fin 1` singleton execution exercising `FragAction.wakeupSingleton` (`0` messages, `0` combines).
2. `K₂` (`Fin 2`, `1` edge) execution reaching `.halted` in `4` steps (`1` merge) with exact
   tightness `s.msgs.total = 6` (`6 + 4 * 2 = 5 * 2 * Nat.log 2 2 + 2 * 1 + 2 = 14`) in
   `FragReachable.halted_msgs_total_add_four_card_le`.
3. Weighted triangle `K₃` (`Fin 3`, weights `10, 20, 30`) exercising `merge`, `absorb` into a
   `searching` fragment, both `rejectChord` modes (`Test` + `Reject` with `dual = false` and
   simultaneous dual `Test` with `dual = true`), `haltSearch`, and nonvacuous instantiations of
   `existsUnique_isMST_of_injOn`, `IsMOE.mem_edgeSet_of_isMST_of_injOn`,
   `FragReachable.halted_branchGraph_isMST`, `FragReachable.rejected_not_isMOE`, and
   `FragReachable.msgs_total_le`.
4. 6-vertex two-wing graph (`Fin 6`, `7` edges, distinct weights `11, 17, 21, 26, 37, 38, 41` after
   [GallagerHumbletSpira1983], Fig. 1, p. 70) exercising two level-`0` merges, level-`1`
   `completeSearch` with positive `changeRootHops = 1`, `absorb` into a `found` fragment without
   re-searching, level-`1` → level-`2` mutual-MOE `merge`, dual-`Test` chord rejection, and
   `haltSearch` at the unique 5-edge MST.
5. Equal-weight `K₃` witness (`w _ = 1`, dropping `Set.InjOn w G.edgeSet`) exhibiting two distinct
   MSTs `T₁ ≠ T₂` and instantiating `IsMST.exists_sup_edge_of_isMOE` (§2 Property 1 without
   distinct weights).
-/
set_option linter.privateModule false

namespace CslibFrontierTests.Distributed.MinimumSpanningTree

open SimpleGraph Cslib Cslib.Distributed.MinimumSpanningTree

/-! ### 1. `Fin 1` singleton (`wakeupSingleton`, `0` messages) -/

def fin1Trace : List (FragAction (Fin 1)) :=
  [.wakeupSingleton 0]

theorem fin1_singleton_execution :
    ∃ s, runFragTrace? (⊥ : SimpleGraph (Fin 1)) (fun _ => 0) (initFragState (Fin 1)) fin1Trace =
        some s ∧
      s.Halted ∧ s.branchEdges = ∅ ∧ s.msgs.total = 0 ∧
      (fin1Trace.filter FragAction.isCombine).length = 0 := by
  decide

/-! ### 2. `K₂` (`Fin 2`) tight `6`-message execution -/

def k2Weight : Sym2 (Fin 2) → ℕ := fun _ => 10

def k2Trace : List (FragAction (Fin 2)) :=
  [ .wakeup 0 s(0, 1)
  , .wakeup 1 s(0, 1)
  , .merge ⟨{0}, 0, none, .found s(0, 1)⟩ ⟨{1}, 0, none, .found s(0, 1)⟩ s(0, 1)
  , .haltSearch ⟨{0, 1}, 1, some s(0, 1), .searching⟩ ]

def k2Final : FragState (Fin 2) :=
  (runFragTrace? (⊤ : SimpleGraph (Fin 2)) k2Weight (initFragState (Fin 2)) k2Trace).getD
    (initFragState (Fin 2))

theorem k2_execution_and_tight_message_bound :
    runFragTrace? (⊤ : SimpleGraph (Fin 2)) k2Weight (initFragState (Fin 2)) k2Trace =
      some k2Final ∧
    k2Final.Halted ∧
    k2Final.branchEdges = {s(0, 1)} ∧
    k2Final.rejectedEdges = ∅ ∧
    k2Final.msgs = { connect := 2, initiate := 2, report := 2 } ∧
    k2Final.msgs.total = 6 ∧
    k2Final.msgs.total + 4 * Fintype.card (Fin 2) =
      5 * Fintype.card (Fin 2) * Nat.log 2 (Fintype.card (Fin 2)) +
        2 * (⊤ : SimpleGraph (Fin 2)).edgeFinset.card + 2 := by
  decide

/-! ### 3. Weighted triangle `K₃` (`Fin 3`, weights `10, 20, 30`) and theorem instantiations -/

def k3Weight : Sym2 (Fin 3) → ℕ := fun e =>
  if e = s(0, 1) then 10
  else if e = s(1, 2) then 20
  else if e = s(0, 2) then 30
  else 100

theorem k3_connected : (⊤ : SimpleGraph (Fin 3)).Connected := by
  refine ⟨fun u v => ?_⟩
  by_cases huv : u = v
  · exact huv ▸ ⟨Walk.nil⟩
  · exact ⟨Walk.cons huv Walk.nil⟩

theorem k3_injOn : Set.InjOn k3Weight (⊤ : SimpleGraph (Fin 3)).edgeSet := by
  intro e₁ he₁ e₂ he₂ heq
  rw [← mem_edgeFinset] at he₁ he₂
  revert e₁ e₂
  decide

def k3SpanFrag : Fragment (Fin 3) :=
  ⟨{0, 1} ∪ {2}, 1, some s(0, 1), .searching⟩

def k3Trace (dual : Bool) : List (FragAction (Fin 3)) :=
  [ .wakeup 0 s(0, 1)
  , .wakeup 1 s(0, 1)
  , .wakeup 2 s(1, 2)
  , .merge ⟨{0}, 0, none, .found s(0, 1)⟩ ⟨{1}, 0, none, .found s(0, 1)⟩ s(0, 1)
  , .absorb ⟨{2}, 0, none, .found s(1, 2)⟩ ⟨{0, 1}, 1, some s(0, 1), .searching⟩
  , .rejectChord k3SpanFrag s(0, 2) dual
  , .haltSearch k3SpanFrag ]

def k3Final (dual : Bool) : FragState (Fin 3) :=
  (runFragTrace? (⊤ : SimpleGraph (Fin 3)) k3Weight (initFragState (Fin 3)) (k3Trace dual)).getD
    (initFragState (Fin 3))

theorem k3_both_rejection_modes_succeed :
    runFragTrace? (⊤ : SimpleGraph (Fin 3)) k3Weight (initFragState (Fin 3)) (k3Trace false) =
      some (k3Final false) ∧
    runFragTrace? (⊤ : SimpleGraph (Fin 3)) k3Weight (initFragState (Fin 3)) (k3Trace true) =
      some (k3Final true) ∧
    (k3Final false).Halted ∧ (k3Final true).Halted ∧
    (k3Final false).branchEdges = {s(0, 1), s(1, 2)} ∧
    (k3Final true).branchEdges = {s(0, 1), s(1, 2)} ∧
    (k3Final false).rejectedEdges = {s(0, 2)} ∧
    (k3Final true).rejectedEdges = {s(0, 2)} ∧
    (k3Final false).msgs = { connect := 3, initiate := 3, test := 1, reject := 1, report := 3 } ∧
    (k3Final true).msgs = { connect := 3, initiate := 3, test := 2, reject := 0, report := 3 } ∧
    ((k3Trace false).filter FragAction.isCombine).length = 2 := by
  decide

theorem k3_reachable_final (dual : Bool) :
    FragReachable (⊤ : SimpleGraph (Fin 3)) k3Weight (k3Final dual) := by
  have hrun : runFragTrace? (⊤ : SimpleGraph (Fin 3)) k3Weight (initFragState (Fin 3))
      (k3Trace dual) = some (k3Final dual) := by
    cases dual <;> decide
  exact ⟨k3Trace dual, (runFragTrace?_eq_some_iff_mTr _ _ _ _ _).mp hrun⟩

/-- Nonvacuous instantiation of `existsUnique_isMST_of_injOn`,
`IsMOE.mem_edgeSet_of_isMST_of_injOn`, `FragReachable.halted_branchGraph_isMST`,
`FragReachable.rejected_not_isMOE`, `FragReachable.msgs_total_le`, and agreement with sequential
`Kruskal.kruskalGraph` (`Kruskal.isMST_iff_eq_toSimpleGraph_kruskalGraph_of_injOn`) on
`(K₃, k3Weight)`. -/
theorem k3_mst_and_protocol_theorems :
    (∃! T, IsMST (⊤ : SimpleGraph (Fin 3)) k3Weight T) ∧
    IsMST (⊤ : SimpleGraph (Fin 3)) k3Weight (k3Final false).branchGraph ∧
    (k3Final false).branchGraph =
      Cslib.Algorithms.Lean.Kruskal.toSimpleGraph
        (Cslib.Algorithms.Lean.Kruskal.kruskalGraph (⊤ : SimpleGraph (Fin 3)) k3Weight) ∧
    edgeWeightSum (k3Final false).branchGraph k3Weight = 30 ∧
    (∀ S : Finset (Fin 3), ¬ IsMOE (⊤ : SimpleGraph (Fin 3)) k3Weight S s(0, 2)) ∧
    (k3Final false).msgs.total ≤
      5 * Fintype.card (Fin 3) * Nat.log 2 (Fintype.card (Fin 3)) +
        2 * (⊤ : SimpleGraph (Fin 3)).edgeFinset.card := by
  have hr := k3_reachable_final false
  have hhalt : (k3Final false).Halted := by decide
  have hrej : s(0, 2) ∈ (k3Final false).rejectedEdges := by decide
  obtain ⟨hMST, _⟩ := hr.halted_branchGraph_isMST k3_connected k3_injOn hhalt
  have hkruskal :
      (k3Final false).branchGraph =
        Cslib.Algorithms.Lean.Kruskal.toSimpleGraph
          (Cslib.Algorithms.Lean.Kruskal.kruskalGraph (⊤ : SimpleGraph (Fin 3)) k3Weight) :=
    (Cslib.Algorithms.Lean.Kruskal.isMST_iff_eq_toSimpleGraph_kruskalGraph_of_injOn
      k3_connected k3Weight k3_injOn).mp hMST
  have hsum : edgeWeightSum (k3Final false).branchGraph k3Weight = 30 := by
    rw [edgeWeightSum_eq_sum_edgeFinset]
    decide
  exact ⟨existsUnique_isMST_of_injOn k3_connected k3_injOn, hMST, hkruskal, hsum,
    hr.rejected_not_isMOE k3_connected k3_injOn hrej, hr.msgs_total_le⟩

/-! ### 4. 6-vertex level-2 execution (`changeRootHops > 0` and absorption into `Found`) -/

def figEdgeSet : Finset (Sym2 (Fin 6)) :=
  {s(0, 1), s(4, 5), s(1, 2), s(2, 5), s(0, 2), s(1, 4), s(3, 4)}

def figGraph : SimpleGraph (Fin 6) :=
  SimpleGraph.fromEdgeSet (figEdgeSet : Set (Sym2 (Fin 6)))

instance : DecidableRel figGraph.Adj := by
  unfold figGraph
  infer_instance

def figWeight : Sym2 (Fin 6) → ℕ := fun e =>
  if e = s(0, 1) then 11
  else if e = s(4, 5) then 17
  else if e = s(1, 2) then 21
  else if e = s(2, 5) then 26
  else if e = s(0, 2) then 37
  else if e = s(1, 4) then 38
  else if e = s(3, 4) then 41
  else 100

def figLeft1 : Fragment (Fin 6) := ⟨{0, 1} ∪ {2}, 1, some s(0, 1), .searching⟩
def figLeft1Found : Fragment (Fin 6) := ⟨{0, 1} ∪ {2}, 1, some s(0, 1), .found s(2, 5)⟩
def figRight1 : Fragment (Fin 6) := ⟨{4, 5}, 1, some s(4, 5), .searching⟩
def figRight1Found : Fragment (Fin 6) := ⟨{4, 5}, 1, some s(4, 5), .found s(2, 5)⟩
def figRight1Abs : Fragment (Fin 6) := ⟨{4, 5} ∪ {3}, 1, some s(4, 5), .found s(2, 5)⟩
def figLevel2 : Fragment (Fin 6) :=
  ⟨({0, 1} ∪ {2}) ∪ ({4, 5} ∪ {3}), 2, some s(2, 5), .searching⟩

def figTrace : List (FragAction (Fin 6)) :=
  [ .wakeup 0 s(0, 1)
  , .wakeup 1 s(0, 1)
  , .merge ⟨{0}, 0, none, .found s(0, 1)⟩ ⟨{1}, 0, none, .found s(0, 1)⟩ s(0, 1)
  , .wakeup 2 s(1, 2)
  , .absorb ⟨{2}, 0, none, .found s(1, 2)⟩ ⟨{0, 1}, 1, some s(0, 1), .searching⟩
  , .rejectChord figLeft1 s(0, 2) false
  , .wakeup 4 s(4, 5)
  , .wakeup 5 s(4, 5)
  , .merge ⟨{4}, 0, none, .found s(4, 5)⟩ ⟨{5}, 0, none, .found s(4, 5)⟩ s(4, 5)
  , .completeSearch figLeft1 s(2, 5)
  , .completeSearch figRight1 s(2, 5)
  , .wakeup 3 s(3, 4)
  , .absorb ⟨{3}, 0, none, .found s(3, 4)⟩ figRight1Found
  , .merge figLeft1Found figRight1Abs s(2, 5)
  , .rejectChord figLevel2 s(1, 4) true
  , .haltSearch figLevel2 ]

def figFinal : FragState (Fin 6) :=
  (runFragTrace? figGraph figWeight (initFragState (Fin 6)) figTrace).getD (initFragState (Fin 6))

theorem fig6_level2_execution_and_changeRoot :
    runFragTrace? figGraph figWeight (initFragState (Fin 6)) figTrace = some figFinal ∧
    figFinal.Halted ∧
    figFinal.branchEdges = {s(0, 1), s(4, 5), s(1, 2), s(2, 5), s(3, 4)} ∧
    figFinal.rejectedEdges = {s(0, 2), s(1, 4)} ∧
    figFinal.msgs.changeRoot = 1 ∧
    (figTrace.filter FragAction.isCombine).length = 5 ∧
    figFinal.msgs.total ≤
      5 * Fintype.card (Fin 6) * Nat.log 2 (Fintype.card (Fin 6)) +
        2 * figGraph.edgeFinset.card := by
  decide

/-! ### 5. Equal-weight `K₃` witness: Property 1 without distinct weights and non-uniqueness -/

def k3TreeA : SimpleGraph (Fin 3) :=
  SimpleGraph.fromEdgeSet ({s(0, 1), s(1, 2)} : Set (Sym2 (Fin 3)))

def k3TreeB : SimpleGraph (Fin 3) :=
  SimpleGraph.fromEdgeSet ({s(0, 2), s(1, 2)} : Set (Sym2 (Fin 3)))

instance : DecidableRel k3TreeA.Adj := by unfold k3TreeA; infer_instance
instance : DecidableRel k3TreeB.Adj := by unfold k3TreeB; infer_instance

theorem k3_equal_weight_two_distinct_msts_and_property1 :
    let wUnif : Sym2 (Fin 3) → ℕ := fun _ => 1
    k3TreeA ≠ k3TreeB ∧
    IsMST (⊤ : SimpleGraph (Fin 3)) wUnif k3TreeA ∧
    IsMST (⊤ : SimpleGraph (Fin 3)) wUnif k3TreeB ∧
    ∃ T', IsMST (⊤ : SimpleGraph (Fin 3)) wUnif T' ∧
      (⊥ : SimpleGraph (Fin 3)) ⊔ SimpleGraph.edge 0 2 ≤ T' := by
  intro wUnif
  have hne : k3TreeA ≠ k3TreeB := by
    intro h
    have hadj : k3TreeA.Adj 0 1 := by decide
    have hadjB : k3TreeB.Adj 0 1 := h ▸ hadj
    exact absurd hadjB (by decide)
  have hcard_fin : ∀ H : SimpleGraph (Fin 3), [DecidableRel H.Adj] →
      Fintype.card H.edgeSet = H.edgeFinset.card := fun H _ => by
    rw [← Fintype.card_coe H.edgeFinset]
    exact Fintype.card_congr
      ⟨fun x => ⟨x.1, Finset.mem_coe.mpr (mem_edgeFinset.mpr x.2)⟩,
       fun x => ⟨x.1, mem_edgeFinset.mp (Finset.mem_coe.mp x.2)⟩,
       fun _ => rfl, fun _ => rfl⟩
  have hTreeA : IsSpanningTree (⊤ : SimpleGraph (Fin 3)) k3TreeA := by
    refine ⟨le_top, ?_⟩
    rw [isTree_iff_connected_and_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      hcard_fin k3TreeA]
    refine ⟨⟨fun u v => ?_⟩, by decide⟩
    fin_cases u <;> fin_cases v
    · exact ⟨Walk.nil⟩
    · exact ⟨Walk.cons (by decide : k3TreeA.Adj 0 1) Walk.nil⟩
    · exact ⟨Walk.cons (by decide : k3TreeA.Adj 0 1)
        (Walk.cons (by decide : k3TreeA.Adj 1 2) Walk.nil)⟩
    · exact ⟨Walk.cons (by decide : k3TreeA.Adj 1 0) Walk.nil⟩
    · exact ⟨Walk.nil⟩
    · exact ⟨Walk.cons (by decide : k3TreeA.Adj 1 2) Walk.nil⟩
    · exact ⟨Walk.cons (by decide : k3TreeA.Adj 2 1)
        (Walk.cons (by decide : k3TreeA.Adj 1 0) Walk.nil)⟩
    · exact ⟨Walk.cons (by decide : k3TreeA.Adj 2 1) Walk.nil⟩
    · exact ⟨Walk.nil⟩
  have hTreeB : IsSpanningTree (⊤ : SimpleGraph (Fin 3)) k3TreeB := by
    refine ⟨le_top, ?_⟩
    rw [isTree_iff_connected_and_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      hcard_fin k3TreeB]
    refine ⟨⟨fun u v => ?_⟩, by decide⟩
    fin_cases u <;> fin_cases v
    · exact ⟨Walk.nil⟩
    · exact ⟨Walk.cons (by decide : k3TreeB.Adj 0 2)
        (Walk.cons (by decide : k3TreeB.Adj 2 1) Walk.nil)⟩
    · exact ⟨Walk.cons (by decide : k3TreeB.Adj 0 2) Walk.nil⟩
    · exact ⟨Walk.cons (by decide : k3TreeB.Adj 1 2)
        (Walk.cons (by decide : k3TreeB.Adj 2 0) Walk.nil)⟩
    · exact ⟨Walk.nil⟩
    · exact ⟨Walk.cons (by decide : k3TreeB.Adj 1 2) Walk.nil⟩
    · exact ⟨Walk.cons (by decide : k3TreeB.Adj 2 0) Walk.nil⟩
    · exact ⟨Walk.cons (by decide : k3TreeB.Adj 2 1) Walk.nil⟩
    · exact ⟨Walk.nil⟩
  have hMin : ∀ T : SimpleGraph (Fin 3), IsSpanningTree (⊤ : SimpleGraph (Fin 3)) T →
      edgeWeightSum T wUnif = 2 := by
    intro T hT
    classical
    rw [edgeWeightSum_eq_sum_edgeFinset]
    have hc := hT.2.card_edgeFinset
    simp only [wUnif, Finset.sum_const, smul_eq_mul, mul_one]
    have hfin : Fintype.card (Fin 3) = 3 := rfl
    omega
  have hMSTA : IsMST (⊤ : SimpleGraph (Fin 3)) wUnif k3TreeA :=
    ⟨hTreeA, fun T' hT' => by rw [hMin k3TreeA hTreeA, hMin T' hT']⟩
  have hMSTB : IsMST (⊤ : SimpleGraph (Fin 3)) wUnif k3TreeB :=
    ⟨hTreeB, fun T' hT' => by rw [hMin k3TreeB hTreeB, hMin T' hT']⟩
  have hMOE : IsMOE (⊤ : SimpleGraph (Fin 3)) wUnif {0} s(0, 2) :=
    ⟨⟨by decide, 0, Finset.mem_singleton_self 0, 2, by decide, rfl⟩, fun _ _ => le_rfl⟩
  have hExt := hMSTA.exists_sup_edge_of_isMOE bot_le (fun _ _ h => False.elim h) hMOE
  exact ⟨hne, hMSTA, hMSTB, hExt⟩

end CslibFrontierTests.Distributed.MinimumSpanningTree
