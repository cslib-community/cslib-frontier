/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Trees.ThinTrees
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Trees.TowerTree
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.ProgramUnits

/-!
# The program of the tree of the tower plan

Theorem H.2(d) of [AnthropicVPVNP2026] (p. 46): the tree of the tower plan, its units and the
numbers of its moves are computed by a straight-line program from the numbers of initial units and
the outcomes. The program reads these inputs and runs the stages of the program of the tower plan:
the numbers of the plan (`TowerPlan.counts_stage`, `11 + 8 Y` stages), the tree
(`TowerPlan.tree_stage`, two stages) and the units (`TowerPlan.units_stage`, nine stages), each of
`Y ^ 12` gates.

## Main results

* `exists_treeProgram`: the program of the tree of the tower plan.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Theorem H.2(d), (e), p. 46, and its proof ("For (d)", p. 48); module `Paper.Tree`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Trees

open Finset Cslib.CoveringTower Cut TowerPlan

variable {F : Type*} [CommSemiring F] {h b D J r m Uu A A' U0 U1 : ℕ} {T : Tower h b D J r}
  {R : Routes T m Uu} {ch : Fin A ↪ T.X 0} {FL : VertexLaws F T} {Pl : Placement T ch A'}

/-- **The program of the tree** ([AnthropicVPVNP2026], Theorem H.2(d), (e), p. 46): under the
bounds `ProgramBound` and `UnitBound` for a base `Y` of the letters `Fin K`, a program with one
gate for every number of initial units and every outcome and `(22 + 8 Y) Y ^ 12` more gates
computes the tree of the tower plan, its units and the numbers of its moves. -/
theorem exists_treeProgram (hh : 0 < h) (hb : 0 < b) (lhat : ℕ) {K Y : ℕ} (hY : StepBase K Y)
    (hB : ProgramBound R ch FL U0 U1 Y) (hB' : UnitBound R FL Pl U0 U1 Y 0) {steps : ℕ}
    (hsteps : Fintype.card ((Fin A × Fin A) ⊕ (moves R FL Pl).Channel) +
      (22 + 8 * Y) * Y ^ 12 ≤ steps) :
    Nonempty (TreeProgram (towerPlan R FL Pl lhat U0 U1) (treeParent R FL Pl hh lhat)
      (treeUnits R FL Pl lhat) K steps) := by
  have hU0 (a : Fin A) : U0 < K := hY.lt_of_le <| (Nat.le_mul_of_pos_left U0
    (Nat.mul_pos a.pos a.pos)).trans ((Nat.le_add_right _ _).trans hB.numUnits_le)
  have hU1 (ν : (moves R FL Pl).Channel) : U1 ≤ K := (hY.lt_of_le <| (Nat.le_mul_of_pos_left U1
    (Fintype.card_pos_iff.2 ⟨moveChannelEquiv R FL Pl ν⟩)).trans
      ((Nat.le_add_left _ _).trans hB.numUnits_le)).le
  let e := Fintype.equivFin ((Fin A × Fin A) ⊕ (moves R FL Pl).Channel)
  let inp : Fin (Fintype.card ((Fin A × Fin A) ⊕ (moves R FL Pl).Channel)) →
      (Fin A → Fin A → Fin (U0 + 1)) × ((moves R FL Pl).Channel → Fin U1) → Fin K :=
    fun i x => match e.symm i with
      | .inl q => ⟨x.1 q.1 q.2, (Nat.lt_succ_iff.1 (x.1 q.1 q.2).2).trans_lt (hU0 q.1)⟩
      | .inr ν => ⟨x.2 ν, (x.2 ν).2.trans_le (hU1 ν)⟩
  have hinp (q) : inp (e q) = fun x => match q with
      | .inl q => ⟨x.1 q.1 q.2, (Nat.lt_succ_iff.1 (x.1 q.1 q.2).2).trans_lt (hU0 q.1)⟩
      | .inr ν => ⟨x.2 ν, (x.2 ν).2.trans_le (hU1 ν)⟩ := by
    simp only [inp, Equiv.symm_apply_apply]
  have hS : SlpN inp (Fintype.card ((Fin A × Fin A) ⊕ (moves R FL Pl).Channel) + 0 * Y ^ 12)
      (Set.range fun i x => (inp i x : ℕ)) := by
    rw [zero_mul, add_zero]
    exact SlpN.inputs inp
  have hi : InputsIn (fun x => initialCounts x.1) (fun x => outcomeOf R FL Pl x.2)
      (Set.range fun i x => (inp i x : ℕ)) :=
    ⟨fun a c => ⟨e (.inl (a, c)), by simp only [hinp]; rfl⟩, fun ν => ⟨e (.inr
      ((moveChannelEquiv R FL Pl).symm ν)), by simp only [hinp]; rfl⟩⟩
  have hR := InputBound.ofPlan (R := R) (FL := FL) (Pl := Pl)
    (Prod.fst : (Fin A → Fin A → Fin (U0 + 1)) × ((moves R FL Pl).Channel → Fin U1) → _)
    Prod.snd
  obtain ⟨H1, s1, u1, f1⟩ := counts_stage (lhat := lhat) hY hB hR hb hS hi
  obtain ⟨H2, s2, u2, f2⟩ := tree_stage hY hB hh (fun x τ => loadGiven_le_numUnits
    (hR.initial_le x) (hR.outcome_le x) _ τ) s1 f1.load f1.toChoicesIn
  obtain ⟨H3, s3, u3, f3⟩ := units_stage hY hB hB' s2 (f1.mono u2)
  have hi3 := hi.mono (u1.trans (u2.trans u3))
  refine ⟨⟨_, inp, H3, s3.le hY.zero_lt (hsteps.trans_eq' (by ring)), fun i => ?_,
    hi3.initial, fun ν => ?_, fun p q => ?_, fun p => u3 (f2.parentUnits _), f3.cur,
    fun z => f3.given (moveSlotEquiv R FL Pl z), fun y => f3.count (moveOrder R ch FL y),
    fun y => f3.good (moveOrder R ch FL y)⟩⟩
  · obtain ⟨q, rfl⟩ := e.surjective i
    rcases q with ⟨a, c⟩ | ν
    exacts [.inl ⟨a, c, fun _ _ => by simp only [hinp]⟩, .inr ⟨ν, fun _ _ => by simp only [hinp]⟩]
  · simpa [outcomeOf] using hi3.outcome (moveChannelEquiv R FL Pl ν)
  · convert u3 (f2.parent (Pl.party.symm p) (Pl.party.symm q)) using 3
    simp only [treeParent, ← Equiv.eq_symm_apply]
    rfl

end Cslib.Circuits.Arithmetic.Separation.Trees
