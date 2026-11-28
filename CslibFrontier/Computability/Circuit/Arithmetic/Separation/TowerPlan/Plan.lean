/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.Counts
public import CslibFrontier.Foundations.Combinatorics.CoveringTower.Rank
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Fin

/-!
# The tower plan

The tower plan of [AnthropicVPVNP2026] (proof of Theorem H.2; module `Nc.Tow.Plan`) as a
`Cut.Plan` for the moves `moves`. The units given at the slot of a relay that is used are the
alive units whose target is the input of the relay. At a vertex, for the kind of law that is
used, the alive units on a pair of places are numbered by their rank and divided among the slots
on that pair, `moveCount` units for every slot.

## Main definitions

* `PlanUnit`, `initialCounts`, `outcomeOf`: the units of the play, and the numbers of initial
  units and the outcomes as natural numbers.
* `unitTarget`, `IsAlive`, `aliveUnits`, `unitIndex`, `unitRank`: the target of a unit, the
  alive units, and the rank of a unit among the alive units with the same target.
* `VertexLaws.slotRank`, `slotInput`, `givenUnits`: the number of a slot among the slots on its
  pair, the target of the units of a slot, and the units given at a slot.
* `towerPlan`: the plan.

## Main results

* `load_eq_card`: the load of a target is the number of alive units with that target.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Theorem H.2 (proof: "One stage"); module `Nc.Tow.Plan`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.TowerPlan

open Finset Cslib.CoveringTower Cut

variable {F : Type*} [CommSemiring F] {h b D J r m Uu A A' U0 U1 : ℕ} {T : Tower h b D J r}

/-- The number of a slot of a law among the slots on the same pair of places. -/
@[expose] noncomputable def VertexLaws.slotRank (FL : VertexLaws F T) (d : FL.Kind)
    (e : (FL.law d).Slot) : ℕ :=
  rk (fun e => (Fintype.equivFin (FL.law d).Slot e : ℕ)) (FL.slotPair d) univ e

variable (R : Routes T m Uu) {ch : Fin A ↪ T.X 0} (FL : VertexLaws F T) (Pl : Placement T ch A')
  (lhat : ℕ)

/-- The units of the play of the tower plan. -/
abbrev PlanUnit (U0 U1 : ℕ) : Type := UnitId A U0 (moves R FL Pl).Channel U1

/-- The numbers of initial units, as natural numbers. -/
@[expose] def initialCounts (n : Fin A → Fin A → Fin (U0 + 1)) : Fin A → Fin A → ℕ :=
  fun a c => n a c

/-- The outcomes on the channels of the moves of the plan, as natural numbers. -/
@[expose] noncomputable def outcomeOf (o : (moves R FL Pl).Channel → Fin U1) :
    MoveChannel R ch FL → ℕ :=
  fun ν => o ((moveChannelEquiv R FL Pl).symm ν)

variable {R FL Pl} in
/-- The outcome of a channel of a move of the plan is the outcome of the channel of the play. -/
@[simp]
theorem outcomeOf_moveOrder (o : (moves R FL Pl).Channel → Fin U1)
    (x : Fin (Fintype.card (Move R ch FL))) (ν : (moveOrder R ch FL x).law.Channel) :
    outcomeOf R FL Pl o ⟨moveOrder R ch FL x, ν⟩ = o ⟨x, ν⟩ :=
  congrArg (fun ν => (o ν : ℕ)) ((Equiv.symm_apply_eq _).2 rfl)

/-- The target of a unit. -/
@[expose] noncomputable def unitTarget : PlanUnit R FL Pl U0 U1 → Target T m A
  | .init a c k => initialTarget R ch a c k
  | .new ν _ => (moveChannelEquiv R FL Pl ν).1.target (moveChannelEquiv R FL Pl ν).2

/-- The target of the units given at a slot: the input of a relay, and the end segments on the
pair of the slot at the vertex of a law move. -/
@[expose] def slotInput : MoveSlot R ch FL → Target T m A
  | ⟨.relay x _, _⟩ => x.input
  | ⟨.vertex l, e⟩ => .segment l.stage l.type l.vertex (FL.slotPair l.kind e)

variable (n : Fin A → Fin A → Fin (U0 + 1)) (o : (moves R FL Pl).Channel → Fin U1)

/-- The unit is alive: an initial unit that there is, if no base party has too many units, and
an alive unit of a channel. -/
@[expose] def IsAlive : PlanUnit R FL Pl U0 U1 → Prop
  | .init a c k => InitialBound lhat (initialCounts n) ∧ (k : ℕ) < n a c
  | .new ν k => (k : ℕ) < alive lhat (initialCounts n) (outcomeOf R FL Pl o)
      (moveChannelEquiv R FL Pl ν)

noncomputable instance : DecidablePred (IsAlive R FL Pl lhat n o)
  | .init .. => inferInstanceAs (Decidable (_ ∧ _))
  | .new .. => inferInstanceAs (Decidable (_ < _))

/-- The set of alive units. -/
noncomputable def aliveUnits : Finset (PlanUnit R FL Pl U0 U1) :=
  univ.filter (IsAlive R FL Pl lhat n o)

/-- The enumeration of the units. -/
noncomputable def unitIndex (u : PlanUnit R FL Pl U0 U1) : ℕ :=
  Fintype.equivFin (PlanUnit R FL Pl U0 U1) u

/-- The rank of a unit among the alive units with the same target. -/
@[expose] noncomputable def unitRank (u : PlanUnit R FL Pl U0 U1) : ℕ :=
  rk (unitIndex R FL Pl) (unitTarget R FL Pl) (aliveUnits R FL Pl lhat n o) u

/-- The units given at a slot. At the slot of a relay that is used: the alive units whose target
is its input. At a slot of the law move that is used at a vertex: the alive end segments on its
pair whose rank is in the window of the slot. -/
noncomputable def givenUnits : MoveSlot R ch FL → Finset (PlanUnit R FL Pl U0 U1)
  | ⟨.relay x _, _⟩ =>
    if x.Active (load lhat (initialCounts n) (outcomeOf R FL Pl o)) then
      (aliveUnits R FL Pl lhat n o).filter fun u => unitTarget R FL Pl u = x.input
    else ∅
  | ⟨.vertex l, e⟩ =>
    if l.IsPicked (load lhat (initialCounts n) (outcomeOf R FL Pl o)) then
      (aliveUnits R FL Pl lhat n o).filter fun u =>
        unitTarget R FL Pl u = .segment l.stage l.type l.vertex (FL.slotPair l.kind e) ∧
        FL.slotRank l.kind e *
            moveCount lhat (initialCounts n) (outcomeOf R FL Pl o) (.vertex l) ≤
          unitRank R FL Pl lhat n o u ∧
        unitRank R FL Pl lhat n o u < (FL.slotRank l.kind e + 1) *
          moveCount lhat (initialCounts n) (outcomeOf R FL Pl o) (.vertex l)
    else ∅

/-- **The tower plan.** -/
@[expose] noncomputable def towerPlan (U0 U1 : ℕ) : Plan (moves R FL Pl) U0 U1 where
  given n o z := givenUnits R FL Pl lhat n o (moveSlotEquiv R FL Pl z)
  count n o x :=
    moveCount lhat (initialCounts n) (outcomeOf R FL Pl o) (moveOrder R ch FL x)
  Good n o x :=
    GoodOutcome lhat (initialCounts n) (outcomeOf R FL Pl o) (moveOrder R ch FL x)

variable {R FL Pl lhat n o}

theorem unitIndex_injective :
    Function.Injective (unitIndex R FL Pl : PlanUnit R FL Pl U0 U1 → ℕ) := fun _ _ huv =>
  (Fintype.equivFin _).injective (Fin.ext huv)

@[simp]
theorem mem_aliveUnits {u : PlanUnit R FL Pl U0 U1} :
    u ∈ aliveUnits R FL Pl lhat n o ↔ IsAlive R FL Pl lhat n o u := by
  simp [aliveUnits]

theorem mem_givenUnits_relay {x : Relay T m A} {hx : x.Occurs R ch} {e : Unit}
    {u : PlanUnit R FL Pl U0 U1} : u ∈ givenUnits R FL Pl lhat n o ⟨.relay x hx, e⟩ ↔
      x.Active (load lhat (initialCounts n) (outcomeOf R FL Pl o)) ∧
        IsAlive R FL Pl lhat n o u ∧ unitTarget R FL Pl u = x.input := by
  simp only [givenUnits]
  split_ifs with ha <;> simp [ha]

theorem mem_givenUnits_vertex {l : VertexMove FL} {e : (FL.law l.kind).Slot}
    {u : PlanUnit R FL Pl U0 U1} :
    u ∈ givenUnits R FL Pl lhat n o (⟨.vertex l, e⟩ : MoveSlot R ch FL) ↔
      l.IsPicked (load lhat (initialCounts n) (outcomeOf R FL Pl o)) ∧
        IsAlive R FL Pl lhat n o u ∧
        unitTarget R FL Pl u = .segment l.stage l.type l.vertex (FL.slotPair l.kind e) ∧
        FL.slotRank l.kind e *
            moveCount lhat (initialCounts n) (outcomeOf R FL Pl o) (.vertex l) ≤
          unitRank R FL Pl lhat n o u ∧
        unitRank R FL Pl lhat n o u < (FL.slotRank l.kind e + 1) *
          moveCount lhat (initialCounts n) (outcomeOf R FL Pl o) (.vertex l) := by
  simp only [givenUnits]
  split_ifs with ha <;> simp [ha]

/-- The units given at a slot are alive and have the target of the slot. -/
theorem isAlive_of_mem_givenUnits {z : MoveSlot R ch FL} {u : PlanUnit R FL Pl U0 U1}
    (hu : u ∈ givenUnits R FL Pl lhat n o z) :
    IsAlive R FL Pl lhat n o u ∧ unitTarget R FL Pl u = slotInput R FL z := by
  rcases z with ⟨⟨x, hx⟩ | l, e⟩
  · exact (mem_givenUnits_relay.1 hu).2
  · exact ⟨(mem_givenUnits_vertex.1 hu).2.1, (mem_givenUnits_vertex.1 hu).2.2.1⟩

private theorem sum_fin_ite_lt_and {N c : ℕ} (hc : c ≤ N) (P : ℕ → Prop) [DecidablePred P] :
    (∑ k : Fin N, if (k : ℕ) < c ∧ P k then 1 else 0) = ((range c).filter P).card := by
  rw [Fin.sum_univ_eq_sum_range (fun k => if k < c ∧ P k then 1 else 0), ← card_filter]
  congr 1
  ext k
  simp only [mem_filter, mem_range]
  exact ⟨fun hk => hk.2, fun hk => ⟨by omega, hk⟩⟩

/-- The load of a target is the number of alive units with that target. -/
theorem load_eq_card (τ : Target T m A) :
    load lhat (initialCounts n) (outcomeOf R FL Pl o) τ =
      ((aliveUnits R FL Pl lhat n o).filter fun u => unitTarget R FL Pl u = τ).card := by
  rw [aliveUnits, filter_filter, card_filter, UnitId.sum_eq, load, loadGiven]
  congr 1
  · unfold initialLoad
    split_ifs with hv
    · refine sum_congr rfl fun a _ => sum_congr rfl fun c _ => ?_
      refine (sum_fin_ite_lt_and (n a c).is_le _).symm.trans ?_
      exact sum_congr rfl fun k _ => if_congr (by simp [IsAlive, hv, unitTarget]) rfl rfl
    · exact (sum_eq_zero fun a _ => sum_eq_zero fun c _ => sum_eq_zero fun k _ =>
        ite_eq_right fun hk => hv hk.1.1).symm
  · rw [← (moveChannelEquiv R FL Pl).sum_comp]
    refine sum_congr rfl fun ν _ => ?_
    have hle : alive lhat (initialCounts n) (outcomeOf R FL Pl o)
        (moveChannelEquiv R FL Pl ν) ≤ U1 :=
      (aliveGiven_le _ _).trans (by simp [outcomeOf])
    refine ((sum_congr rfl fun k _ => if_congr Iff.rfl rfl rfl).trans ((sum_fin_ite_lt_and hle
      fun _ => (moveChannelEquiv R FL Pl ν).1.target (moveChannelEquiv R FL Pl ν).2 = τ).trans
        ?_)).symm
    rw [filter_const]
    split_ifs <;> simp [alive]

/-- A slot is given at most as many units as its move uses. -/
theorem card_givenUnits_le (z : MoveSlot R ch FL) :
    (givenUnits R FL Pl lhat n o z : Finset (PlanUnit R FL Pl U0 U1)).card ≤
      moveCount lhat (initialCounts n) (outcomeOf R FL Pl o) z.1 := by
  rcases z with ⟨⟨x, hx⟩ | l, e⟩
  · rw [moveCount_eq, countOfLoad, givenUnits]
    split_ifs
    · rw [load_eq_card]
    · simp
  · rw [givenUnits]
    split_ifs
    · refine (card_rk_le unitIndex_injective _ _ _ _).trans ?_
      rw [Nat.add_mul, Nat.one_mul, Nat.add_sub_cancel_left]
    · simp

end Cslib.Circuits.Arithmetic.Separation.TowerPlan
