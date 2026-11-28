/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.ProgramChoices
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.PlayMoves

/-!
# The program of the tower plan: the units

For the numbers `nI x` of initial units and the outcomes `oI x` of the play of the tower plan of
[AnthropicVPVNP2026] (Theorem H.2(d); module `Nc.Tow.Slp4`), the program computes, after the
numbers of the plan (`counts_stage`), in nine more stages, the units of the play: which units are
alive, their ranks, the units given at every slot and their number, which units are left at the
end, and which outcomes are good (`UnitsIn`, `units_stage`). The numbers below `TM` serve the
units of zeros at the slots that are given fewer units than their move uses. The numbers of slots
and of units and `TM` are at most `Y` (`UnitBound`).

## Main definitions

* `UnitBound`: the bounds for the units.
* `UnitsIn`: the units of the play are among the computed functions.

## Main results

* `InputBound.ofPlan`: the inputs of the play are in range.
* `units_stage`: the units take nine stages.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Theorem H.2(d) and (e), p. 46, and the proof ("For (d)", p. 48); module `Nc.Tow.Slp4`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.TowerPlan

open Finset Cslib.CoveringTower Cut

variable {F : Type*} [CommSemiring F] {h b D J r m Uu A A' U0 U1 : ℕ} {T : Tower h b D J r}
  {R : Routes T m Uu} {ch : Fin A ↪ T.X 0} {FL : VertexLaws F T} {Pl : Placement T ch A'}
  {lhat : ℕ} {Inp : Type} {K Y N p c TM : ℕ} {inp : Fin N → Inp → Fin K} {H H' : Set (Inp → ℕ)}
  {nI : Inp → Fin A → Fin A → Fin (U0 + 1)} {oI : Inp → (moves R FL Pl).Channel → Fin U1}

variable (R FL Pl) in
/-- The bounds for the units: the numbers of slots and of units, and `TM`, are at most `Y`. -/
structure UnitBound (U0 U1 Y TM : ℕ) : Prop where
  card_slot_le : Fintype.card (MoveSlot R ch FL) ≤ Y
  card_unit_le : Fintype.card (PlanUnit R FL Pl U0 U1) ≤ Y
  padding_le : TM ≤ Y

variable (nI oI) in
/-- The numbers of initial units and the outcomes of the play are at most `U0` and `U1`. -/
theorem InputBound.ofPlan :
    InputBound (fun x => initialCounts (nI x)) (fun x => outcomeOf R FL Pl (oI x)) U0 U1 :=
  ⟨fun x a c => Nat.le_of_lt_succ (nI x a c).isLt, fun x _ => (oI x _).isLt.le⟩

/-- The units of the play are among the functions `H`: the indicators of the units given at the
slots, the numbers of units of the moves, the indicators of the numbers `k < TM` below them and,
at every slot, between the number of units given and the number of units of the move, the
indicators of the units left at the end and of the good outcomes, and the indicator of the bound
for the initial units. -/
structure UnitsIn (nI : Inp → Fin A → Fin A → Fin (U0 + 1))
    (oI : Inp → (moves R FL Pl).Channel → Fin U1) (lhat TM : ℕ) (H : Set (Inp → ℕ)) : Prop where
  given : ∀ (z : MoveSlot R ch FL) (u : PlanUnit R FL Pl U0 U1),
    {x | u ∈ givenUnits R FL Pl lhat (nI x) (oI x) z}.indicator 1 ∈ H
  count : ∀ mv : Move R ch FL,
    (fun x => moveCount lhat (initialCounts (nI x)) (outcomeOf R FL Pl (oI x)) mv) ∈ H
  lt_count : ∀ (mv : Move R ch FL) (k : Fin TM), {x | (k : ℕ) <
    moveCount lhat (initialCounts (nI x)) (outcomeOf R FL Pl (oI x)) mv}.indicator 1 ∈ H
  padding : ∀ (z : MoveSlot R ch FL) (k : Fin TM),
    {x | (givenUnits R FL Pl lhat (nI x) (oI x) z).card ≤ k ∧ (k : ℕ) <
      moveCount lhat (initialCounts (nI x)) (outcomeOf R FL Pl (oI x)) z.1}.indicator 1 ∈ H
  cur : ∀ u : PlanUnit R FL Pl U0 U1, {x | u ∈ (towerPlan R FL Pl lhat U0 U1).cur (nI x) (oI x)
    (Fintype.card (Move R ch FL))}.indicator 1 ∈ H
  good : ∀ mv : Move R ch FL, {x | GoodOutcome lhat (initialCounts (nI x))
    (outcomeOf R FL Pl (oI x)) mv}.indicator 1 ∈ H
  allGood : {x | ∀ mv : Move R ch FL, GoodOutcome lhat (initialCounts (nI x))
    (outcomeOf R FL Pl (oI x)) mv}.indicator 1 ∈ H
  initialBound : {x | InitialBound lhat (initialCounts (nI x))}.indicator 1 ∈ H

theorem UnitsIn.mono (hu : UnitsIn nI oI lhat TM H) (hH : H ⊆ H') : UnitsIn nI oI lhat TM H' :=
  ⟨fun z u => hH (hu.given z u), fun mv => hH (hu.count mv), fun mv k => hH (hu.lt_count mv k),
    fun z k => hH (hu.padding z k), fun u => hH (hu.cur u), fun mv => hH (hu.good mv),
    hH hu.allGood, hH hu.initialBound⟩

variable (hY : StepBase K Y) (hB : ProgramBound R ch FL U0 U1 Y)
  (hB' : UnitBound R FL Pl U0 U1 Y TM)
include hY hB hB'

omit hB hB' in
private theorem costP_isAlive (ha : CountsIn (fun x => initialCounts (nI x))
      (fun x => outcomeOf R FL Pl (oI x)) lhat H) (u : PlanUnit R FL Pl U0 U1) :
    CostP K H (Y ^ 2) fun x => IsAlive R FL Pl lhat (nI x) (oI x) u := by
  rcases u with ⟨a, c, k⟩ | ⟨ν, k⟩
  · exact hY.and (CostP.of_mem ha.initialBound) (hY.rel1 (k < ·) (Cost.of_mem (ha.initial a c)))
  · exact hY.rel1 (k < ·) (Cost.of_mem (ha.alive _))

omit hB in
private theorem cost_unitRank
    (hal : ∀ u, {x | IsAlive R FL Pl lhat (nI x) (oI x) u}.indicator 1 ∈ H)
    (u : PlanUnit R FL Pl U0 U1) :
    Cost K H (Y ^ 2) fun x => unitRank R FL Pl lhat (nI x) (oI x) u := by
  refine (hY.card_filter (univ.filter fun v => unitTarget R FL Pl v = unitTarget R FL Pl u ∧
    unitIndex R FL Pl v < unitIndex R FL Pl u) ((card_filter_le _ _).trans hB'.card_unit_le)
      fun v _ => CostP.of_mem (hal v)).congr fun x => ?_
  rw [unitRank, rk_eq]
  congr 1
  ext v
  simp only [mem_filter, mem_univ, true_and, mem_aliveUnits]
  tauto

omit hB hB' in
private theorem costP_mem_givenUnits (ha : CountsIn (fun x => initialCounts (nI x))
      (fun x => outcomeOf R FL Pl (oI x)) lhat H)
    (hal : ∀ u, {x | IsAlive R FL Pl lhat (nI x) (oI x) u}.indicator 1 ∈ H)
    (hrk : ∀ u, (fun x => unitRank R FL Pl lhat (nI x) (oI x) u) ∈ H) (z : MoveSlot R ch FL)
    (u : PlanUnit R FL Pl U0 U1) :
    CostP K H (Y ^ 5) fun x => u ∈ givenUnits R FL Pl lhat (nI x) (oI x) z := by
  rcases z with ⟨⟨y, hy⟩ | l, e⟩
  · exact (hY.and (costP_active hY ha.chosenType y) (hY.and (CostP.of_mem (hal u))
      (hY.constP _))).congr fun x => mem_givenUnits_relay.symm
  · exact (hY.and (CostP.of_mem (ha.isPicked l)) (hY.and (CostP.of_mem (hal u)) (hY.and
      (hY.constP _) (hY.and
        (hY.rel (fun s t => FL.slotRank l.kind e * s ≤ t) (Cost.of_mem (ha.count _))
          (Cost.of_mem (hrk u)))
        (hY.rel (fun s t => t < (FL.slotRank l.kind e + 1) * s) (Cost.of_mem (ha.count _))
          (Cost.of_mem (hrk u))))))).congr fun x => mem_givenUnits_vertex.symm

omit hB in
private theorem costP_mem_cur (ha : CountsIn (fun x => initialCounts (nI x))
      (fun x => outcomeOf R FL Pl (oI x)) lhat H)
    (hg : ∀ z u, {x | u ∈ givenUnits R FL Pl lhat (nI x) (oI x) z}.indicator 1 ∈ H)
    (u : PlanUnit R FL Pl U0 U1) : CostP K H (Y ^ 4) fun x =>
      u ∈ (towerPlan R FL Pl lhat U0 U1).cur (nI x) (oI x) (Fintype.card (Move R ch FL)) := by
  have h1 : CostP K H (Y ^ 3) fun x => u.index < u.count (nI x) (oI x) := by
    rcases u with ⟨a, c, k⟩ | ⟨ν, k⟩
    · exact hY.rel1 (k < ·) (Cost.of_mem (ha.initial a c))
    · exact (hY.rel1 (fun s => k < s + 1) (Cost.of_mem (ha.outcome (moveChannelEquiv R FL Pl ν))))
        |>.congr fun x => by simp [outcomeOf, UnitId.index, UnitId.count]
  refine (hY.and h1 (hY.not (hY.exists_univ hB'.card_slot_le fun z => CostP.of_mem (hg z u))))
    |>.congr fun x => ?_
  rw [Plan.mem_cur, Plan.mem_seenAt_end]
  refine and_congr_right' ⟨fun h z _ hz => h ⟨_, hz⟩, fun h ⟨z, hz⟩ =>
    h ((moveSlotEquiv R FL Pl).symm z) ((moveSlotEquiv R FL Pl).symm z).1.isLt ?_⟩
  simpa [towerPlan] using hz

omit hB' in
private theorem costP_goodOutcome (ha : CountsIn (fun x => initialCounts (nI x))
      (fun x => outcomeOf R FL Pl (oI x)) lhat H) (mv : Move R ch FL) :
    CostP K H (Y ^ 4) fun x =>
      GoodOutcome lhat (initialCounts (nI x)) (outcomeOf R FL Pl (oI x)) mv := by
  rcases mv with ⟨y, hy⟩ | l
  · exact hY.forall_univ (by simpa using (show 2 ≤ Y by have := hY.three_le; omega)) fun ν =>
      hY.rel (· = ·) (Cost.of_mem (ha.outcome _)) (Cost.of_mem (ha.count _))
  · exact hY.and (hY.rel (fun q t => r * b * q ≤ FL.lengthBound * t ^ 2)
      (Cost.of_mem (ha.sqOutcome l)) (Cost.of_mem (ha.count _)))
      (hY.forall_univ (hB.card_law_channel_le l) fun ν =>
        hY.rel (· ≤ ·) (Cost.of_mem (ha.count _)) (Cost.of_mem (ha.outcome _)))

/-- **The units** take nine stages: the indicators of the alive units, their ranks, the
indicators of the units given at the slots and their numbers, the indicators of the numbers below
`TM` that are below the numbers of units of the moves, and below them and at least the numbers
of units given at the slots, the indicators of the units left at the end, and those of the good
outcomes of every move and of all moves. -/
theorem units_stage (hS : SlpN inp (p + c * Y ^ 12) H)
    (ha : CountsIn (fun x => initialCounts (nI x)) (fun x => outcomeOf R FL Pl (oI x)) lhat H) :
    ∃ H', SlpN inp (p + (c + 9) * Y ^ 12) H' ∧ H ⊆ H' ∧ UnitsIn nI oI lhat TM H' := by
  have hun : Fintype.card (PlanUnit R FL Pl U0 U1) ≤ Y ^ 1 := by simpa using hB'.card_unit_le
  have hsq {α β : Type} [Fintype α] [Fintype β] (h1 : Fintype.card α ≤ Y)
      (h2 : Fintype.card β ≤ Y) : Fintype.card (α × β) ≤ Y ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul h1 h2
  have hTM : Fintype.card (Fin TM) ≤ Y := by simpa using hB'.padding_le
  obtain ⟨H1, s1, u1, f1⟩ := hY.stage hS
    (fun u => {x | IsAlive R FL Pl lhat (nI x) (oI x) u}.indicator 1) hun
    (fun u => costP_iff.1 (costP_isAlive hY ha u)) (by norm_num)
  obtain ⟨H2, s2, u2, f2⟩ := hY.stage s1 (fun u x => unitRank R FL Pl lhat (nI x) (oI x) u) hun
    (cost_unitRank hY hB' f1) (by norm_num)
  have a2 := ha.mono (u1.trans u2)
  obtain ⟨H3, s3, u3, f3⟩ := hY.stage s2 (fun q : MoveSlot R ch FL × PlanUnit R FL Pl U0 U1 =>
      {x | q.2 ∈ givenUnits R FL Pl lhat (nI x) (oI x) q.1}.indicator 1)
    (hsq hB'.card_slot_le hB'.card_unit_le)
    (fun q => costP_iff.1 (costP_mem_givenUnits hY a2 (fun u => u2 (f1 u)) f2 q.1 q.2))
    (by norm_num)
  have g3 z u : {x | u ∈ givenUnits R FL Pl lhat (nI x) (oI x) z}.indicator 1 ∈ H3 := f3 (z, u)
  obtain ⟨H4, s4, u4, f4⟩ := hY.stage s3
    (fun z x => (givenUnits R FL Pl lhat (nI x) (oI x) z).card) (e := 1)
    (by simpa using hB'.card_slot_le) (fun z => (hY.card_filter (a := 0) univ hB'.card_unit_le
      fun u _ => CostP.of_mem (g3 z u)).congr fun x => by rw [filter_mem_eq_inter, univ_inter])
    (by norm_num)
  have a4 := a2.mono (u3.trans u4)
  obtain ⟨H5, s5, u5, f5⟩ := hY.stage s4 (fun q : Move R ch FL × Fin TM => {x | (q.2 : ℕ) <
      moveCount lhat (initialCounts (nI x)) (outcomeOf R FL Pl (oI x)) q.1}.indicator 1)
    (hsq hB.card_move_le hTM)
    (fun q => costP_iff.1 (hY.rel1 (a := 0) _ (Cost.of_mem (a4.count q.1)))) (by norm_num)
  obtain ⟨H6, s6, u6, f6⟩ := hY.stage s5 (fun q : MoveSlot R ch FL × Fin TM =>
      {x | (givenUnits R FL Pl lhat (nI x) (oI x) q.1).card ≤ q.2 ∧ (q.2 : ℕ) <
        moveCount lhat (initialCounts (nI x)) (outcomeOf R FL Pl (oI x)) q.1.fst}.indicator 1)
    (hsq hB'.card_slot_le hTM) (fun q => costP_iff.1 (hY.and (hY.rel1 (a := 0) (· ≤ q.2)
      (Cost.of_mem (u5 (f4 q.1)))) (hY.rel1 _ (Cost.of_mem (u5 (a4.count q.1.fst))))))
    (by norm_num)
  have a6 := a4.mono (u5.trans u6)
  obtain ⟨H7, s7, u7, f7⟩ := hY.stage s6 (fun u => {x | u ∈ (towerPlan R FL Pl lhat U0 U1).cur
      (nI x) (oI x) (Fintype.card (Move R ch FL))}.indicator 1) hun
    (fun u => costP_iff.1 (costP_mem_cur hY hB' a6 (fun z u => u6 (u5 (u4 (g3 z u)))) u))
    (by norm_num)
  have a7 := a6.mono u7
  obtain ⟨H8, s8, u8, f8⟩ := hY.stage s7 (fun mv => {x | GoodOutcome lhat (initialCounts (nI x))
      (outcomeOf R FL Pl (oI x)) mv}.indicator 1) (e := 1) (by simpa using hB.card_move_le)
    (fun mv => costP_iff.1 (costP_goodOutcome hY hB a7 mv)) (by norm_num)
  obtain ⟨H9, s9, u9, f9⟩ := hY.stage s8 (κ := Unit) (fun _ => {x | ∀ mv,
      GoodOutcome lhat (initialCounts (nI x)) (outcomeOf R FL Pl (oI x)) mv}.indicator 1)
    (e := 0) (by simp) (fun _ => costP_iff.1 (hY.forall_univ (a := 0) hB.card_move_le
      fun mv => CostP.of_mem (f8 mv))) (by norm_num)
  have v := u8.trans u9
  exact ⟨H9, s9, u1.trans (u2.trans (u3.trans (u4.trans (u5.trans (u6.trans (u7.trans v)))))),
    fun z u => v (u7 (u6 (u5 (u4 (g3 z u))))), fun mv => v (a7.count mv),
    fun mv k => v (u7 (u6 (f5 (mv, k)))), fun z k => v (u7 (f6 (z, k))), fun u => v (f7 u),
    fun mv => u9 (f8 mv), f9 (), v a7.initialBound⟩

end Cslib.Circuits.Arithmetic.Separation.TowerPlan
