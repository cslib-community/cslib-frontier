/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Cslib.Computability.Circuit.Boolean.Basic
import CslibFrontier.Computability.Circuit.Frontier.Arborescence

/-! Checked clients for `SimpleGraph.ArborescenceIndep` and `Frontier/Arborescence.lean`. -/

open Set Cslib.Circuits Cslib.Circuits.Frontier

namespace CslibFrontierTests.FrontierArborescence

/-! ### Out-forest acyclicity and Tree-DP bounds on `K_{1, 3}` and `K_{1, 4}` -/

/-- Directed `3`-leaf root star on `Fin 4` (`0 → 1, 2, 3`). -/
private def arcStar3 (u w : Fin 4) : Prop :=
  u = 0 ∧ w ≠ 0

private theorem arcStar3_rank ⦃u w : Fin 4⦄ (h : arcStar3 u w) : u.val < w.val := by
  rcases h with ⟨rfl, hw⟩
  exact Fin.pos_iff_ne_zero.mpr hw

private theorem arcStar3_subsingleton (w : Fin 4) : {u : Fin 4 | arcStar3 u w}.Subsingleton := by
  rintro u₁ ⟨rfl, -⟩ u₂ ⟨rfl, -⟩
  rfl

private theorem arcStar3_out_int (w : Fin 4) (h : ∃ u, arcStar3 u w) :
    {v : Fin 4 | arcStar3 w v}.ncard ≤ 2 := by
  obtain ⟨_, rfl, hw⟩ := h
  have hemp : {v : Fin 4 | arcStar3 w v} = ∅ := by
    ext v
    simp [arcStar3, hw]
  simp [hemp]

private theorem arcStar3_out_root (r : Fin 4) (_ : ¬∃ u, arcStar3 u r) :
    {v : Fin 4 | arcStar3 r v}.ncard ≤ 3 := by
  calc {v : Fin 4 | arcStar3 r v}.ncard
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

example : (SimpleGraph.fromRel arcStar3).IsAcyclic :=
  SimpleGraph.fromRel_isAcyclic_of_subsingleton arcStar3_rank arcStar3_subsingleton

example : SimpleGraph.arborescenceCappedEdges arcStar3 =
    (SimpleGraph.fromRel arcStar3).edgeSet.ncard :=
  SimpleGraph.arborescenceCappedEdges_eq_ncard_edgeSet arcStar3_rank
    arcStar3_out_int arcStar3_out_root

example : Real.logb 2 ((SimpleGraph.fromRel arcStar3).indepSetCount : ℝ) ≤
    4 - (53 / 200 : ℝ) * ((SimpleGraph.fromRel arcStar3).edgeSet.ncard : ℝ) -
      (33 / 1000 : ℝ) * ((SimpleGraph.arborescenceActiveRoots arcStar3).ncard : ℝ) := by
  have h := SimpleGraph.logb_indepSetCount_fromRel_le arcStar3_rank arcStar3_subsingleton
    arcStar3_out_int arcStar3_out_root
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h
  exact h

example : ((SimpleGraph.fromRel arcStar3).indepSetCount : ℝ) ≤
    (2 : ℝ) ^ ((4 : ℝ) - (53 / 200 : ℝ) * ((SimpleGraph.fromRel arcStar3).edgeSet.ncard : ℝ) -
      (33 / 1000 : ℝ) * ((SimpleGraph.arborescenceActiveRoots arcStar3).ncard : ℝ)) := by
  have h := SimpleGraph.indepSetCount_fromRel_le_rpow arcStar3_rank arcStar3_subsingleton
    arcStar3_out_int arcStar3_out_root
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h
  exact h

/-- Directed `4`-leaf root star on `Fin 5` (`0 → 1, 2, 3, 4`), exercising degree capping at `3`. -/
private def arcStar4 (u w : Fin 5) : Prop :=
  u = 0 ∧ w ≠ 0

example : Real.logb 2 ((SimpleGraph.fromRel arcStar4).indepSetCount : ℝ) ≤
    5 - (53 / 200 : ℝ) * (SimpleGraph.arborescenceCappedEdges arcStar4 : ℝ) -
      (33 / 1000 : ℝ) * ((SimpleGraph.arborescenceActiveRoots arcStar4).ncard : ℝ) := by
  have h := SimpleGraph.logb_indepSetCount_fromRel_le_capped
    (arc := arcStar4) (rk := fun u : Fin 5 => u.val)
    (fun _ _ ⟨hu, hw⟩ => hu ▸ Fin.pos_iff_ne_zero.mpr hw)
    (fun _ _ ⟨hu₁, _⟩ _ ⟨hu₂, _⟩ => hu₁.trans hu₂.symm)
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h
  exact h

/-! ### Circuit frontier arborescence and `1 / 4`-clause amortized bounds -/

/-- Fan-in-2 Boolean circuit on `3` inputs: `g₀ = x₀ ∧ x₁`, `g₁ = g₀ ∨ x₂`. -/
private def arbProg : Program Boolean.signature 3 2 :=
  ((Program.empty : Program Boolean.signature 3 0).gate
    ⟨Boolean.Op.and, ![Wire.input 0, Wire.input 1]⟩).gate
    ⟨Boolean.Op.or, ![Wire.gate 0, Wire.input 2]⟩

private def arbCircuit : Circuit Boolean.signature 3 1 where
  program := arbProg
  outputs _ := .gate 1

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
          (fun e => arbCircuit.program.trace Boolean.interpretation x e.signal.1)) '' X).ncard : ℝ)
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
          (fun e => arbCircuit.program.trace Boolean.interpretation x e.signal.1)) '' X).ncard : ℝ)
      ≤ ((cutWires arbCircuit (π.initial t)).ncard : ℝ) -
        (1 / 4 : ℝ) * (twoCappedClauseEdges arbCircuit.program Boolean.interpretation
          (cutWires arbCircuit (π.initial t)) : ℝ) :=
  logb_ncard_frontierValues_le_quarter_sub arbCircuit.fanInAtMost_two Boolean.interpretation
    (fun _ => {true}) π t X

example (sg sz sa sb : Bool) :
    (1 / 2 : ℝ) * (((sg != sz).toNat : ℝ) + ((sg != sa).toNat : ℝ) + ((sg != sb).toNat : ℝ)) -
      (1 / 4 : ℝ) * ((((sg != sz) && (sg != sa)).toNat : ℝ) +
        (((sg != sz) && (sg != sb)).toNat : ℝ)) =
      (1 / 4 : ℝ) * ((sg != sz).toNat : ℝ) +
        (3 / 8 : ℝ) * (((sg != sa).toNat : ℝ) + ((sg != sb).toNat : ℝ)) +
        (1 / 8 : ℝ) * (((sz != sa).toNat : ℝ) + ((sz != sb).toNat : ℝ)) :=
  half_cut_sub_quarter_clause_eq sg sz sa sb

end CslibFrontierTests.FrontierArborescence
