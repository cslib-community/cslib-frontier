/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (regression tests)

import Cslib.Computability.Circuit.Boolean.Basic
import CslibFrontier.Computability.Circuit.Frontier.Arborescence
import Mathlib.Tactic.FinCases

/-! Checked `module` clients for `SimpleGraph.ArborescenceIndep` and `Frontier/Arborescence.lean`.
-/

set_option linter.privateModule false

open Set Cslib.Circuits Cslib.Circuits.Frontier

namespace CslibFrontierTests.FrontierArborescence

/-! ### Out-forest acyclicity and Tree-DP bounds on `K_{1, 3}` and `K_{1, 4}` -/

/-- Directed `3`-leaf root star on `Fin 4` (`0 → 1, 2, 3`). -/
private def arcStar3 : Digraph (Fin 4) where
  Adj u w := u = 0 ∧ w ≠ 0

private theorem arcStar3_isBranching : arcStar3.IsBranching :=
  Digraph.IsBranching.of_rank (rk := fun u : Fin 4 => u.val)
    (fun _ _ ⟨hu, hw⟩ => hu ▸ Fin.pos_iff_ne_zero.mpr hw)
    (fun _ _ _ ⟨hu₁, _⟩ ⟨hu₂, _⟩ => hu₁.trans hu₂.symm)

private theorem arcStar3_out_int (w : Fin 4) (h : ∃ u, arcStar3.Adj u w) :
    {v : Fin 4 | arcStar3.Adj w v}.ncard ≤ 2 := by
  obtain ⟨_, rfl, hw⟩ := h
  have hemp : {v : Fin 4 | arcStar3.Adj w v} = ∅ := by
    ext v
    simp [arcStar3, hw]
  simp [hemp]

private theorem arcStar3_out_root (r : Fin 4) (_ : ¬∃ u, arcStar3.Adj u r) :
    {v : Fin 4 | arcStar3.Adj r v}.ncard ≤ 3 := by
  calc {v : Fin 4 | arcStar3.Adj r v}.ncard
      ≤ ({1, 2, 3} : Set (Fin 4)).ncard := by
        refine ncard_le_ncard (fun v hv => ?_) (toFinite _)
        have hv0 : v ≠ 0 := hv.2
        have hvlt := v.isLt
        simp only [mem_insert_iff, mem_singleton_iff, Fin.ext_iff]
        have hv0' : v.val ≠ 0 := fun h => hv0 (Fin.ext h)
        omega
    _ ≤ 3 := by
      refine (ncard_insert_le _ _).trans ?_
      refine Nat.add_le_add_right ((ncard_insert_le _ _).trans ?_) 1
      simp

example : (SimpleGraph.fromRel arcStar3.Adj).IsAcyclic :=
  arcStar3_isBranching.toSimpleGraph_isAcyclic

example : SimpleGraph.arborescenceCappedEdges arcStar3 =
    (SimpleGraph.fromRel arcStar3.Adj).edgeSet.ncard :=
  SimpleGraph.arborescenceCappedEdges_eq_ncard_edgeSet arcStar3_isBranching
    arcStar3_out_int arcStar3_out_root

example : Real.logb 2 ((SimpleGraph.fromRel arcStar3.Adj).indepSetCount : ℝ) ≤
    4 - (53 / 200 : ℝ) * ((SimpleGraph.fromRel arcStar3.Adj).edgeSet.ncard : ℝ) -
      (33 / 1000 : ℝ) * ((SimpleGraph.arborescenceActiveRoots arcStar3).ncard : ℝ) := by
  have h := SimpleGraph.logb_indepSetCount_fromRel_le arcStar3_isBranching
    arcStar3_out_int arcStar3_out_root
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h
  exact h

example : ((SimpleGraph.fromRel arcStar3.Adj).indepSetCount : ℝ) ≤
    (2 : ℝ) ^ ((4 : ℝ) - (53 / 200 : ℝ) * ((SimpleGraph.fromRel arcStar3.Adj).edgeSet.ncard : ℝ) -
      (33 / 1000 : ℝ) * ((SimpleGraph.arborescenceActiveRoots arcStar3).ncard : ℝ)) := by
  have h := SimpleGraph.indepSetCount_fromRel_le_rpow arcStar3_isBranching
    arcStar3_out_int arcStar3_out_root
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h
  exact h

/-- Directed `4`-leaf root star on `Fin 5` (`0 → 1, 2, 3, 4`), exercising degree capping at `3`. -/
private def arcStar4 : Digraph (Fin 5) where
  Adj u w := u = 0 ∧ w ≠ 0

private theorem arcStar4_isBranching : arcStar4.IsBranching :=
  Digraph.IsBranching.of_rank (rk := fun u : Fin 5 => u.val)
    (fun _ _ ⟨hu, hw⟩ => hu ▸ Fin.pos_iff_ne_zero.mpr hw)
    (fun _ _ _ ⟨hu₁, _⟩ ⟨hu₂, _⟩ => hu₁.trans hu₂.symm)

example : SimpleGraph.arborescenceCappedEdges arcStar4 = 3 := by
  rw [SimpleGraph.arborescenceCappedEdges, finsum_eq_sum_of_fintype]
  have h0 : {v : Fin 5 | arcStar4.Adj 0 v} = ((Finset.univ.erase (0 : Fin 5) : Finset (Fin 5)) :
      Set (Fin 5)) := by
    ext v
    simp [arcStar4]
  have h0_card : {v : Fin 5 | arcStar4.Adj 0 v}.ncard = 4 := by
    rw [h0, ncard_coe_finset, Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ,
      Fintype.card_fin]
  have hno0 : ¬∃ u : Fin 5, arcStar4.Adj u 0 := by
    rintro ⟨_, -, hne⟩
    exact hne rfl
  have hne0 : ∀ w : Fin 5, w ≠ 0 → {v : Fin 5 | arcStar4.Adj w v} = ∅ := fun w hw => by
    ext v
    simp [arcStar4, hw]
  rw [Finset.sum_eq_single (0 : Fin 5)]
  · simp [h0_card, hno0]
  · intro w _ hw
    simp [hne0 w hw]
  · intro h
    exact absurd (Finset.mem_univ 0) h

example : (SimpleGraph.arborescenceActiveRoots arcStar4).ncard = 1 := by
  have heq : SimpleGraph.arborescenceActiveRoots arcStar4 = {(0 : Fin 5)} := by
    ext r
    simp only [SimpleGraph.arborescenceActiveRoots, arcStar4, mem_ofPred_eq, mem_singleton_iff]
    constructor
    · rintro ⟨_, _, hr, -⟩
      exact hr
    · rintro rfl
      exact ⟨fun ⟨_, _, hne⟩ => hne rfl, 1, rfl, by decide⟩
  rw [heq, ncard_singleton]

example : Real.logb 2 ((SimpleGraph.fromRel arcStar4.Adj).indepSetCount : ℝ) ≤
    5 - (53 / 200 : ℝ) * (SimpleGraph.arborescenceCappedEdges arcStar4 : ℝ) -
      (33 / 1000 : ℝ) * ((SimpleGraph.arborescenceActiveRoots arcStar4).ncard : ℝ) := by
  have h := SimpleGraph.logb_indepSetCount_fromRel_le_capped arcStar4_isBranching
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h
  exact h

/-! ### Circuit frontier arborescence, concrete non-empty `D₀`, and `1 / 4`-clause bounds -/

/-- Fan-in-2 Boolean circuit on `3` inputs: `g₀ = x₀ ∧ x₁`, `g₁ = g₀ ∨ x₂`. -/
private def arbProg : Program Boolean.signature 3 2 :=
  ((Program.empty : Program Boolean.signature 3 0).gate
    ⟨Boolean.Op.and, ![Wire.input 0, Wire.input 1]⟩).gate
    ⟨Boolean.Op.or, ![Wire.gate 0, Wire.input 2]⟩

private abbrev arbCircuit : Circuit Boolean.signature 3 1 where
  program := arbProg
  outputs _ := .gate 1

/-- Singleton vertex cut isolating output gate `g₁`, whose incoming argument edges and outgoing
head edge all cross `arbGate1Cut` so `.gate 1 ∈ depthOneDetermined (cutWires arbCircuit _)`. -/
private def arbGate1Cut : Set (Compiler.Vertex arbCircuit) :=
  {Compiler.Vertex.signal ⟨.gate 1, .output 0⟩}

private theorem gate1_mem_depthOneDetermined_arbGate1Cut :
    (.gate 1 : Wire 3 2) ∈
      arbCircuit.program.depthOneDetermined (cutWires arbCircuit arbGate1Cut) := by
  let sig1 : Compiler.Signal arbCircuit := ⟨.gate 1, .output 0⟩
  have hhead_cut : Compiler.head sig1 ∈ (Compiler.graph arbCircuit).edgeCut arbGate1Cut := by
    simp only [Multigraph.mem_edgeCut, arbGate1Cut, mem_singleton_iff, Compiler.graph_src,
      Compiler.graph_tgt]
    have hs : Compiler.src (Compiler.head sig1) = .signal sig1 := rfl
    have ht : Compiler.tgt (Compiler.head sig1) ≠ .signal sig1 := by
      intro h
      exact Compiler.loopless (Compiler.head sig1) (hs.trans h.symm)
    exact fun hiff => ht (hiff.mp hs)
  refine ⟨⟨Compiler.head sig1, hhead_cut, rfl⟩, 1, rfl, fun a => ?_⟩
  have harg_cut : Compiler.argEdge (c := arbCircuit) (.output 0) a ∈
      (Compiler.graph arbCircuit).edgeCut arbGate1Cut := by
    simp only [Multigraph.mem_edgeCut, arbGate1Cut, mem_singleton_iff, Compiler.graph_src,
      Compiler.graph_tgt]
    have ht : Compiler.tgt (Compiler.argEdge (c := arbCircuit) (.output 0) a) = .signal sig1 :=
      Compiler.tgt_deliverEdge _
    have hs : Compiler.src (Compiler.argEdge (c := arbCircuit) (.output 0) a) ≠ .signal sig1 := by
      intro h
      exact Compiler.loopless (Compiler.argEdge (c := arbCircuit) (.output 0) a) (h.trans ht.symm)
    exact fun hiff => hs (hiff.mpr ht)
  exact ⟨Compiler.argEdge (c := arbCircuit) (.output 0) a, harg_cut,
    by simp [Compiler.consumed]⟩

example : (arbCircuit.program.depthOneDetermined (cutWires arbCircuit arbGate1Cut)).Nonempty :=
  ⟨.gate 1, gate1_mem_depthOneDetermined_arbGate1Cut⟩

example : twoCappedClauseEdges arbCircuit.program Boolean.interpretation
      (cutWires arbCircuit arbGate1Cut) ≤
    clauseCappedEdges arbCircuit.program Boolean.interpretation
      (cutWires arbCircuit arbGate1Cut \
        arbCircuit.program.depthOneDetermined (cutWires arbCircuit arbGate1Cut)) +
      4 * (arbCircuit.program.depthOneDetermined (cutWires arbCircuit arbGate1Cut)).ncard :=
  twoCappedClauseEdges_le_add_four_mul arbCircuit.fanInAtMost_two Boolean.interpretation
    (cutWires arbCircuit arbGate1Cut)

example (P : Set (Compiler.Vertex arbCircuit)) :
    (u2ClauseGraph arbCircuit.program Boolean.interpretation
      (cutWires arbCircuit P \
        arbCircuit.program.depthOneDetermined (cutWires arbCircuit P))).IsAcyclic :=
  isAcyclic_u2ClauseGraph_cutWires_sdiff arbCircuit.fanInAtMost_two Boolean.interpretation P
    Subset.rfl

example (P : Set (Compiler.Vertex arbCircuit)) :
    (u2ClauseGraph arbCircuit.program Boolean.interpretation
      (cutWires arbCircuit P \
        arbCircuit.program.forwardDetermined (cutWires arbCircuit P))).IsAcyclic :=
  isAcyclic_u2ClauseGraph_cutWires_sdiff arbCircuit.fanInAtMost_two Boolean.interpretation P
    (arbCircuit.program.depthOneDetermined_subset_forwardDetermined _)

example (π : Layout (Compiler.Vertex arbCircuit)) (t : ℕ) (X : Set (Fin 3 → Bool)) :
    Real.logb 2 (((fun x =>
        (Compiler.network arbCircuit Boolean.interpretation (fun _ => {true})).frontierValues π t
          (fun e => arbCircuit.program.trace Boolean.interpretation x e.signal.val)) ''
              X).ncard : ℝ)
      ≤ ((cutWires arbCircuit (π.initial t)).ncard : ℝ) -
        ((arbCircuit.program.forwardDetermined (cutWires arbCircuit (π.initial t))).ncard : ℝ) -
        (53 / 200 : ℝ) * (clauseCappedEdges arbCircuit.program Boolean.interpretation
          (cutWires arbCircuit (π.initial t) \
            arbCircuit.program.forwardDetermined (cutWires arbCircuit (π.initial t))) : ℝ) -
        (33 / 1000 : ℝ) * ((clauseActiveRoots arbCircuit.program Boolean.interpretation
          (cutWires arbCircuit (π.initial t) \
            arbCircuit.program.forwardDetermined (cutWires arbCircuit (π.initial t)))).ncard : ℝ) :=
  logb_ncard_frontierValues_le_arborescence arbCircuit.fanInAtMost_two Boolean.interpretation
    (fun _ => {true}) π t
    (arbCircuit.program.depthOneDetermined_subset_forwardDetermined _) Subset.rfl X

example (π : Layout (Compiler.Vertex arbCircuit)) (t : ℕ) (X : Set (Fin 3 → Bool)) :
    Real.logb 2 (((fun x =>
        (Compiler.network arbCircuit Boolean.interpretation (fun _ => {true})).frontierValues π t
          (fun e => arbCircuit.program.trace Boolean.interpretation x e.signal.val)) ''
              X).ncard : ℝ)
      ≤ ((cutWires arbCircuit (π.initial t)).ncard : ℝ) -
        (1 / 4 : ℝ) * (twoCappedClauseEdges arbCircuit.program Boolean.interpretation
          (cutWires arbCircuit (π.initial t)) : ℝ) :=
  logb_ncard_frontierValues_le_quarter_sub arbCircuit.fanInAtMost_two Boolean.interpretation
    (fun _ => {true}) π t X

end CslibFrontierTests.FrontierArborescence
