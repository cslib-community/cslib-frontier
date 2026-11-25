/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.PlayMoves
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.Capacity
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.EndUnits
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.EverHeld
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.ProgramUnits
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.Rules
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.Transfer
import CslibFrontier.Foundations.Algebra.BigOperators.Sym
import CslibFrontier.Foundations.GroupTheory.SLTower.Tower
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators

/-! Tests of the tower plan, as a client that sees only the public statements.

* The relay law: its tables, its identity for one bit, and `Cut.Law.pow` for `B` bits.
* The times and the targets of relays in an arbitrary tower.
* A tower with one chamber on every level and no edges, with routes, laws at its vertices and a
  placement: this shows that `VertexLaws` and `Placement` are inhabited. Its plan has no moves, so
  `towerPlan_ok` applies to it with the bound `0`.
* A tower with two chambers joined by one edge, and one unit from the base party `0` to the base
  party `1`: the unit goes over the edge, it is given at the slot of the relay of the edge, the
  load of the edge and the number of units of the relay are positive, and by the rule
  `holder_given` of `towerPlan_ok` that slot joins the parties `0` and `1`.
* The capacity of that tower: the edge is at both chambers (`Tower.incidentSum`) and its type is
  chosen (`Tower.IsChosenType`); with the ratio `D = 2` the tower and its laws satisfy `StageRate`
  at the rate `1`, the boundary case of `towerPlan_ok_moveCap`; `startBound` and `moveCap` on its
  numbers are `10` and `33`, and the relay of the edge uses between `1` and `moveCap` units.
* The units of that plan in the end, with the outcome `1` on every channel: the relay of the edge
  is the only move and uses the one unit on the edge, so the outcomes are good and its channels
  have one alive unit each. The new unit `0` of its first channel is assigned to the chamber
  `false`, and by `card_assignedUnits_le` it is the only unit between that chamber and its parent,
  within `edgeUnitBound` at the rate `1`; the initial unit is not current after all moves
  (`unitTarget_eq_done_of_mem_cur`).
* The sizes of that tower, its routes and its laws are at most `2` (`SizeBound`): its tree has
  three nodes, and a placement with one extra party exists (`exists_placement`). With one initial
  unit between two base parties and one unit on every channel, its plan has at most `1092` units
  and satisfies the bounds of the program (`ProgramBound`, `UnitBound`) for `Y = 1100`, and from
  any program for the inputs, `counts_stage`, `tree_stage` and `units_stage` compute its numbers,
  its tree and its units.
* For an arbitrary tower, under the hypotheses of the statements: `towerPlan_ok` bounds the units
  given at a slot by `cap`; no alive unit of a channel of a law move is current after all moves;
  the units that a party ever holds, exactly; possible outcomes are good, in the form that
  `Cut.Plan.value_moves` needs; and for good outcomes, the units that the party of a node ever
  holds.
* Laws at the vertices of other towers: the laws of the tower with one edge, at the vertices of
  the tower without edges, with the same constants; the laws at the vertices of a tower of
  `SL_h(F₂)` at the vertices of every other one; and the `3` pairs of different elements of
  `Fin 3`, from the `6` ordered ones. -/

set_option linter.privateModule false

namespace CslibFrontierTests.SeparationTowerPlan

open Finset Cslib Cslib.CoveringTower Cslib.Circuits Cslib.Circuits.Arithmetic.Separation
  Cslib.Circuits.Arithmetic.Separation.Cut Cslib.Circuits.Arithmetic.Separation.TowerPlan

variable {F : Type} [CommSemiring F] {h b D J r m Uu A A' U0 U1 lhat cap : ℕ}

/-! ### The relay law -/

/-- The role `via` of a relay accepts equal bits on its two channels, and only those. -/
example : relayTable ℕ .via (fun _ => true) (fun _ _ => false) = 1 := by simp [relayTable]

example : relayTable ℕ .via (fun _ => true) (fun ν _ => ν.1) = 0 := by simp [relayTable]

example : relayChannelEnd true false = .via ∧ relaySlotEnd () true = .sink := by decide

/-- The identity of the relay for one bit: if the two copies agree, exactly one choice of the two
bits on the channels passes all three tables. -/
example (X : RelayRole → Unit → Bool) (hX : X .source () = X .sink ()) :
    ∑ _i : Unit, ∑ g : Bool → BitString 1,
      ∏ p, relayTable F p (fun e => X p e.1) (fun ν => g ν.1) = 1 :=
  ((relayLaw F).identity X).symm.trans (ite_eq_left fun _ => hX)

/-- The power of the relay law: `B` bits shared by `source` and `sink` are led through `via`. -/
example (B : ℕ) (X : RelayRole → Fin B → Unit → Bool) :
    (if ∀ e k, X .source k e = X .sink k e then (1 : F) else 0) =
      ∑ _i : Fin B → Unit, ∑ g : Bool → (k : Fin B) → BitString 1,
        ∏ p, ∏ k, relayTable F p (fun e => X p k e.1) fun ν => g ν.1 k :=
  (relayLaw F).pow B X

example : (relayLaw F).LengthLE 1 := fun _ _ => le_rfl

/-! ### Relays and targets in an arbitrary tower -/

example : endTime 2 3 = 19 := by decide

section

variable {T : Tower h b D J r} (R : Routes T m Uu) (ch : Fin A ↪ T.X 0) (e : T.Ed J)

/-- The relay of an edge of the last stage goes through the root, at the last time, and its
units stay where they are. -/
example : (Relay.final e : Relay T m A).party R ch .via = .root := rfl

example : (Relay.final e : Relay T m A).time m + 1 = endTime J m := rfl

example : (Relay.final e : Relay T m A).input = .edge (Fin.last J) e := rfl

example (d : Bool) : (Relay.final e : Relay T m A).target R ch d = .done := rfl

/-- The two ends of an edge of the last stage are different nodes. -/
example : (.ofChamber le_rfl (T.e0 e) : T.Node) ≠ .ofChamber le_rfl (T.e1 e) := fun he =>
  absurd (Relay.party_injective (R := R) (ch := ch) (x := .final e) trivial (a₁ := .source)
    (a₂ := .sink) he)
    (by decide)

/-- The units of a channel of a relay are given later than the relay. -/
example (x : Relay T m A) (d : Bool) (y : Relay T m A) (hy : x.target R ch d = .relay y) :
    x.time m < y.time m := by
  simpa [hy, Target.time] using x.time_lt_time_target (R := R) (ch := ch) d

end

/-! ### A tower without edges -/

/-- One chamber on every level, no edges, no types. -/
private def pointTower (r : ℕ) : Tower 0 1 1 0 r where
  X _ := Unit
  Ed _ := Empty
  V _ _ := Empty
  Fl := Unit
  Nr := Empty
  e0 e := e.elim
  e1 e := e.elim
  e_ne e := e.elim
  ty e := e.elim
  card_ed _ _ i := i.elim0
  deg _ _ _ i := i.elim0
  vx i := i.elim0
  co i := i.elim0
  vx_co _ i := i.elim0
  card_fl := rfl
  cN ν := ν.elim
  dN ν := ν.elim
  n_ne ν := ν.elim
  nr _ i := i.elim0
  nr_vx0 _ i := i.elim0
  nr_vx1 _ i := i.elim0
  nr_co _ i := i.elim0
  π c := c
  πE e := e
  πV v := v
  π_ends _ e := e.elim
  π_ty _ e := e.elim
  card_X _ hj := absurd hj (Nat.not_lt_zero _)
  fibre hj := absurd hj (Nat.not_lt_zero _)
  π_vx _ i := i.elim0
  π_co _ i := i.elim0
  host i := i.elim0
  host_inj _ i := i.elim0
  host_vx _ i := i.elim0

/-- The empty routes of the tower without edges. -/
private def pointRoutes (r m : ℕ) : Routes (pointTower r) m 0 where
  rt _ _ := []
  walk _ _ := rfl
  len _ _ := Nat.zero_le _
  use e := e.elim

/-- A law with one role and neither slots nor channels: its identity is `1 = 1`. -/
private def pointLaw (F : Type) [CommSemiring F] : Law F where
  Role := Unit
  Slot := Empty
  Channel := Empty
  Index := Unit
  slotEnd e := e.elim
  slotEnd_ne e := e.elim
  channelEnd ν := ν.elim
  channelEnd_ne ν := ν.elim
  labelLength := 1
  label _ _ := false
  label_injective _ _ _ := rfl
  length _ ν := ν.elim
  table _ _ _ _ := 1
  identity X := by simp
  connected _ _ _ _ := rfl

/-- The laws at the vertices of a tower with one place at a vertex and no near pairs: there are
no pairs of different places, so the law without slots serves every load. -/
private def unitLaws (F : Type) [CommSemiring F] (T : Tower h b D J r) (eF : T.Fl ≃ Unit)
    (eN : T.Nr ≃ Empty) : VertexLaws F T where
  Kind := Unit
  law _ := pointLaw F
  place _ := eF.symm
  nearPair _ := eN.symm
  place_channelEnd _ ν := ν.elim
  labelLength_pos _ := le_rfl
  nonempty_index _ := ⟨()⟩
  scale := 1
  scale_pos := Nat.one_pos
  contraction := 0
  contraction_nonneg := le_rfl
  lengthBound := 0
  lengthBound_le := by simp
  exists_le_card_slot _ _ _ := ⟨(), fun q hq => absurd (Sym2.ind (fun x y =>
    Sym2.mk_isDiag_iff.2 (eF.injective (Subsingleton.elim _ _))) q) hq⟩
  sum_length_sq_le _ _ := by
    have : IsEmpty (pointLaw F).Channel := inferInstanceAs (IsEmpty Empty)
    simp

/-- The one base party at the one chamber of the level `0`. -/
private def pointBase (r : ℕ) : Fin 1 ↪ (pointTower r).X 0 :=
  ⟨fun _ => (), fun _ _ _ => Subsingleton.elim _ _⟩

/-- The chamber is at the base party, and the root at the extra party. -/
private def pointPlacement (r : ℕ) : Placement (pointTower r) (pointBase r) 1 where
  party :=
    { toFun := fun | .root => 1 | .chamber _ _ => 0
      invFun := fun i => if i = 0 then .chamber 0 () else .root
      left_inv := by
        rintro (_ | ⟨j, c⟩)
        · rfl
        · obtain rfl : j = 0 := Fin.ext (Nat.lt_one_iff.1 j.2)
          rfl
      right_inv := by rintro ⟨_ | _ | i, hi⟩ <;> first | rfl | omega }
  party_base a := by
    obtain rfl : a = 0 := Subsingleton.elim _ _
    rfl

/-- The plan of the tower without edges has no moves, and it obeys the rules with the bound
`0`. -/
example (hr : 0 < r) :
    (towerPlan (pointRoutes r m) (unitLaws F _ (Equiv.refl _) (Equiv.refl _)) (pointPlacement r)
      lhat U0 U1).Ok 0 :=
  towerPlan_ok hr Nat.one_pos fun n o mv => by
    rcases mv with ⟨x, hx⟩ | l
    · rcases x with ⟨a, c, γ, s⟩ | ⟨j, i, e⟩ | ⟨j, e, s⟩ | e
      · exact absurd (Subsingleton.elim a c) hx.1
      · exact j.elim0
      · exact j.elim0
      · exact e.elim
    · exact l.stage.elim0

/-! ### A tower with one edge -/

/-- Two chambers on the one level, joined by an edge of the one type; every chamber is a vertex
of its own. Its ratio `D = 2` concerns only the levels below `J = 0`, of which there are none, and
makes the rate `1` admissible (`2 ≤ 1 · D`). -/
@[reducible] private def edgeTower : Tower 1 1 2 0 1 where
  X _ := Bool
  Ed _ := Unit
  V _ _ := Bool
  Fl := Unit
  Nr := Empty
  e0 _ := false
  e1 _ := true
  e_ne _ := Bool.false_ne_true
  ty _ := 0
  card_ed _ _ i := by obtain rfl := Subsingleton.elim i 0; decide
  deg _ _ _ _ := (card_le_univ _).trans le_rfl
  vx _ c := c
  co _ _ := ()
  vx_co _ _ := ⟨fun _ _ h => congrArg Prod.fst h, fun p => ⟨p.1, rfl⟩⟩
  card_fl := rfl
  cN ν := ν.elim
  dN ν := ν.elim
  n_ne ν := ν.elim
  nr _ _ :=
    @Equiv.equivOfIsEmpty _ _ ⟨fun e => e.2 (Subsingleton.elim _ _)⟩ ⟨fun p => p.2.elim⟩
  nr_vx0 _ _ e := absurd (Subsingleton.elim _ _) e.2
  nr_vx1 _ _ e := absurd (Subsingleton.elim _ _) e.2
  nr_co _ _ e := absurd (Subsingleton.elim _ _) e.2
  π c := c
  πE e := e
  πV v := v
  π_ends hj := absurd hj (Nat.not_lt_zero _)
  π_ty hj := absurd hj (Nat.not_lt_zero _)
  card_X _ hj := absurd hj (Nat.not_lt_zero _)
  fibre hj := absurd hj (Nat.not_lt_zero _)
  π_vx hj := absurd hj (Nat.not_lt_zero _)
  π_co hj := absurd hj (Nat.not_lt_zero _)
  host _ v := v
  host_inj hj := absurd hj (Nat.not_lt_zero _)
  host_vx hj := absurd hj (Nat.not_lt_zero _)

/-- The route between the two chambers is the edge. -/
private def edgeRoutes : Routes edgeTower 1 2 where
  rt c c' := if c = c' then [] else [()]
  walk c c' := by
    cases c <;> cases c' <;> first | rfl | exact ⟨Or.inl rfl, rfl⟩ | exact ⟨Or.inr rfl, rfl⟩
  len c c' := by split <;> simp
  use e := by cases e; decide

/-- The base parties `0` and `1` at the chambers `false` and `true`. -/
private def edgeBase : Fin 2 ↪ edgeTower.X 0 := finTwoEquiv.toEmbedding

/-- The chambers at the base parties, and the root at the extra party. -/
private def edgePlacement : Placement edgeTower edgeBase 1 where
  party :=
    { toFun := fun | .root => 2 | .chamber _ c => if c then 1 else 0
      invFun := fun i => if i = 2 then .root else .chamber 0 (decide (i = 1))
      left_inv := by
        rintro (_ | ⟨j, c⟩)
        · rfl
        · obtain rfl : j = 0 := Fin.ext (Nat.lt_one_iff.1 j.2)
          cases c <;> rfl
      right_inv := by decide }
  party_base := by decide

/-- One unit from the base party `0` to the base party `1`, and none between other parties. -/
private def edgeCounts : Fin 2 → Fin 2 → Fin 2 := fun a c => if a < c then 1 else 0

/-- The routes between the two chambers arrive after the first step. -/
private theorem not_one_lt_pl {c c' : Bool} (hc : c ≠ c') (γ : Bool) :
    ¬ 1 < edgeRoutes.pl c c' γ := fun h1 => by
  obtain ⟨_, -, -, hne⟩ := edgeRoutes.exists_edge c c' γ (s := 0) (by omega)
  have := edgeRoutes.pn_ne c c' γ h1
  rw [edgeRoutes.pn_zero] at hne
  cases h : edgeRoutes.pn c c' γ 1 <;> cases c <;> cases c' <;> simp_all

/-- The unit from the party `0` to the party `1` goes over the edge, at the last stage. -/
private theorem initialTarget_edge (k : ℕ) :
    initialTarget edgeRoutes edgeBase 0 1 k = .edge (Fin.last 0) () := by
  have hpl := edgeRoutes.pl_pos Bool.false_ne_true (batchChamber edgeBase 0 k)
  obtain ⟨e, he, -⟩ := edgeRoutes.exists_edge false true (batchChamber edgeBase 0 k) hpl
  have h0 : ¬ (0 < 2 * 1 ∧
      1 < edgeRoutes.pl (edgeBase 0) (edgeBase 1) (batchChamber edgeBase 0 k)) :=
    fun h => not_one_lt_pl Bool.false_ne_true _ h.2
  simp only [initialTarget, show (0 : Fin 2) ≠ 1 by decide, ↓reduceIte, h0, dite_false,
    stepTarget]
  cases e
  simp only [show edgeBase 0 = false from rfl, show edgeBase 1 = true from rfl, he]
  rfl

/-- The laws at the vertices of the tower with one edge. -/
private abbrev edgeLaws (F : Type) [CommSemiring F] : VertexLaws F edgeTower :=
  unitLaws F edgeTower (Equiv.refl _) (Equiv.refl _)

/-- The relay of the edge, a move of the plan. -/
private def edgeRelay : Move edgeRoutes edgeBase (edgeLaws F) := .relay (.final ()) trivial

/-- A move of the plan of the tower with one edge uses at most as many units as there are. -/
private theorem moveCount_le (lhat U0 U1 : ℕ) (n : Fin 2 → Fin 2 → Fin (U0 + 1))
    (o : (moves edgeRoutes (edgeLaws F) edgePlacement).Channel → Fin U1)
    (mv : Move edgeRoutes edgeBase (edgeLaws F)) :
    moveCount lhat (initialCounts n) (outcomeOf _ _ edgePlacement o) mv ≤
      Fintype.card (PlanUnit edgeRoutes (edgeLaws F) edgePlacement U0 U1) := by
  rcases mv with ⟨x, hx⟩ | l
  · rw [moveCount_eq, countOfLoad]
    split_ifs
    · exact (load_eq_card _).trans_le (card_le_univ _)
    · exact Nat.zero_le _
  · exact l.stage.elim0

variable (o : (moves edgeRoutes (edgeLaws F) edgePlacement).Channel → Fin U1)

/-- The unit from the party `0` to the party `1` is given at the slot of the relay of the
edge. -/
private theorem init_mem_givenUnits :
    UnitId.init 0 1 0 ∈ givenUnits edgeRoutes _ edgePlacement 2 edgeCounts o
      ⟨edgeRelay (F := F), ()⟩ :=
  mem_givenUnits_relay.2 ⟨trivial, ⟨by decide, by decide⟩, initialTarget_edge 0⟩

/-- The load of the edge and the number of units of its relay are positive. -/
example : 0 < load 2 (initialCounts edgeCounts) (outcomeOf _ _ edgePlacement o)
      (.edge (Fin.last 0) ()) ∧
    0 < moveCount 2 (initialCounts edgeCounts) (outcomeOf _ _ edgePlacement o) edgeRelay := by
  have hu := init_mem_givenUnits o
  refine ⟨?_, (card_pos.2 ⟨_, hu⟩).trans_le (card_givenUnits_le _)⟩
  rw [load_eq_card]
  exact card_pos.2 ⟨_, mem_filter.2 ⟨mem_aliveUnits.2 (isAlive_of_mem_givenUnits hu).1,
    initialTarget_edge 0⟩⟩

/-- The slot of the relay of the edge. -/
private noncomputable def edgeSlot : (moves edgeRoutes (edgeLaws F) edgePlacement).Slot :=
  (moveSlotEquiv _ _ edgePlacement).symm ⟨edgeRelay, ()⟩

/-- In the tower plan, the unit from the party `0` to the party `1` is given at the slot of the
relay of the edge. -/
private theorem init_mem_given : UnitId.init 0 1 0 ∈
    (towerPlan edgeRoutes (edgeLaws F) edgePlacement 2 1 1).given edgeCounts (fun _ => 0)
      edgeSlot := by
  simpa [towerPlan, edgeSlot] using init_mem_givenUnits (F := F) (U1 := 1) (fun _ => 0)

/-- The plan obeys the rules, and the unit from the party `0` to the party `1` is given at the
slot of the relay of the edge: so that slot joins the parties `0` and `1`. -/
example : s((moves edgeRoutes (edgeLaws F) edgePlacement).slotParty edgeSlot false,
    (moves edgeRoutes (edgeLaws F) edgePlacement).slotParty edgeSlot true) = s(0, 1) := by
  obtain ⟨d, hd⟩ := (towerPlan_ok Nat.one_pos Nat.one_pos
    (moveCount_le (F := F) 2 1 1)).holder_given edgeCounts (fun _ => 0) edgeSlot (.init 0 1 0)
    init_mem_given
  have h0 := hd false
  have h1 := hd true
  cases d <;> simp only [UnitId.holder, Bool.xor_false, Bool.xor_true, Bool.not_false,
    Bool.not_true, Bool.cond_false, Bool.cond_true] at h0 h1 <;> rw [← h0, ← h1] <;> decide

/-! ### The capacity of the tower with one edge -/

/-- Both chambers are ends of the edge: the units between a chamber and its parent are the load
of the edge. -/
example (n : edgeTower.Ed 0 → ℕ) (c : Bool) : edgeTower.incidentSum n c = n () := by
  cases c <;> simp [Tower.incidentSum]

/-- The one type is chosen for the loads of the edges. -/
example : edgeTower.IsChosenType (j := 0) (fun _ => 3) 0 := by decide

/-- The tower with one edge and its laws satisfy the conditions of the stages at the rate `1`:
`1 + 8 · 0 ≤ 1² · 1` and `2 ≤ 1 · 2`. -/
private theorem edgeStageRate : StageRate (edgeLaws F) 1 where
  r_pos := Nat.one_pos
  b_pos := Nat.one_pos
  h_pos := Nat.one_pos
  b_le := by decide
  ρ_pos := one_pos
  one_add_le := by simp [unitLaws]
  two_le := by norm_num

/-- After the start, the edge carries at most `2 * (2 / 2 + 2 * 2) = 10` units: the routes use it
at most `2` times, there are `2` chambers and `2` base parties, and every base party has at most
`2` initial units. -/
example : startBound edgeTower 2 2 2 = 10 := by decide

/-- The bound for the norms is the bound `10` after the start, since the laws have no
contraction; so a move uses at most `1 + 2 + ⌈3 · 1 · 10⌉ = 33` units. -/
example : moveCap (edgeLaws ℕ) 1 2 2 2 = 33 := by
  have hX : Fintype.card (edgeTower.X 0) = 2 := rfl
  norm_num [moveCap, normBound, startBound, unitLaws, hX]

/-- At the rate `1` the tower plan obeys the rules with the bound `moveCap`
(`towerPlan_ok_moveCap`), so the relay of the edge, whose slot is given the unit from the party
`0` to the party `1`, uses between `1` and `moveCap` units. -/
example : 1 ≤ (towerPlan edgeRoutes (edgeLaws F) edgePlacement 2 1 1).count edgeCounts
      (fun _ => 0) edgeSlot.1 ∧
    (towerPlan edgeRoutes (edgeLaws F) edgePlacement 2 1 1).count edgeCounts (fun _ => 0)
      edgeSlot.1 ≤ moveCap (edgeLaws F) 1 2 2 2 :=
  have hP := towerPlan_ok_moveCap (R := edgeRoutes) (Pl := edgePlacement) (lhat := 2) (U0 := 1)
    (U1 := 1) edgeStageRate le_rfl
  ⟨(card_pos.2 ⟨_, init_mem_given⟩).trans_le (hP.card_given_le _ _ _), hP.count_le _ _ _⟩

/-! ### The units in the end, for the tower with one edge -/

/-- The relay of the edge is the only move of the plan: the routes need no relays, and the tower
has no stages. -/
private theorem eq_edgeRelay (mv : Move edgeRoutes edgeBase (edgeLaws F)) : mv = edgeRelay := by
  rcases mv with ⟨⟨a, c, γ, s⟩ | ⟨j, i, e⟩ | ⟨j, e, s⟩ | e, hx⟩ | l
  · exact absurd (by have := hx.2; omega) (not_one_lt_pl (edgeBase.injective.ne hx.1) γ)
  · exact j.elim0
  · exact j.elim0
  · rfl
  · exact l.stage.elim0

/-- The outcome `1` on every channel. -/
private def edgeOutcome : (moves edgeRoutes (edgeLaws F) edgePlacement).Channel → Fin 2 :=
  fun _ => 1

/-- The edge carries one unit, the initial unit from the party `0` to the party `1`: the units of
the channels of the relay of the edge are done. -/
private theorem load_edge :
    load 2 (initialCounts edgeCounts) (outcomeOf _ _ edgePlacement o) (.edge 0 ()) = 1 := by
  rw [load_eq_card, card_eq_one]
  refine ⟨.init 0 1 0, eq_singleton_iff_unique_mem.2 ⟨mem_filter.2
    ⟨mem_aliveUnits.2 ⟨by decide, by decide⟩, initialTarget_edge 0⟩, fun u hu => ?_⟩⟩
  obtain ⟨hu, ht⟩ := mem_filter.1 hu
  rcases u with ⟨a, c, k⟩ | ⟨ν, k⟩
  · obtain ⟨rfl, rfl, rfl⟩ := (by decide : ∀ a c : Fin 2, ∀ k : Fin 1,
      (k : ℕ) < (edgeCounts a c : ℕ) → a = 0 ∧ c = 1 ∧ k = 0) a c k (mem_aliveUnits.1 hu).2
    rfl
  · revert ht
    simp only [unitTarget]
    generalize moveChannelEquiv _ _ edgePlacement ν = w
    obtain ⟨mv, d⟩ := w
    obtain rfl := eq_edgeRelay mv
    simp [edgeRelay, Move.target, Relay.target]

/-- The relay of the edge uses the one unit on the edge. -/
private theorem moveCount_edgeRelay :
    moveCount 2 (initialCounts edgeCounts) (outcomeOf _ _ edgePlacement o) edgeRelay = 1 :=
  (moveCount_eq _).trans (load_edge o)

/-- The relay of the edge, the only move, uses the one unit on the edge; with the outcome `1` on
every channel the outcomes are good, and both channels of the relay have one alive unit. -/
example : moveCount 2 (initialCounts edgeCounts) (outcomeOf _ _ edgePlacement edgeOutcome)
      (edgeRelay (F := F)) = 1 ∧
    (∀ x, (towerPlan edgeRoutes (edgeLaws F) edgePlacement 2 1 2).Good edgeCounts edgeOutcome x) ∧
    ∀ β, alive 2 (initialCounts edgeCounts) (outcomeOf _ _ edgePlacement edgeOutcome)
      ⟨edgeRelay (F := F), β⟩ = 1 := by
  refine ⟨moveCount_edgeRelay _, fun x => ?_, fun _ =>
    alive_eq_of_goodOutcome fun _ => (moveCount_edgeRelay _).symm⟩
  change GoodOutcome _ _ _ (moveOrder edgeRoutes edgeBase (edgeLaws F) x)
  rw [eq_edgeRelay (moveOrder edgeRoutes edgeBase (edgeLaws F) x)]
  exact fun _ => (moveCount_edgeRelay _).symm

/-- The first channel of the relay of the edge. -/
private noncomputable def edgeChannel : (moves edgeRoutes (edgeLaws F) edgePlacement).Channel :=
  (moveChannelEquiv _ _ edgePlacement).symm ⟨edgeRelay, false⟩

/-- The new unit `0` of the first channel of the relay of the edge is alive, and its units are done
between the chamber `false` and its parent: the unit is assigned to that chamber. -/
private theorem new_mem_assignedUnits_edge :
    (.new edgeChannel 0 : PlanUnit edgeRoutes (edgeLaws F) edgePlacement 1 2) ∈
      assignedUnits edgeRoutes (edgeLaws F) edgePlacement 2 edgeCounts edgeOutcome
        (.ofChamber le_rfl false) := by
  simp only [new_mem_assignedUnits, edgeChannel, Equiv.apply_symm_apply]
  refine ⟨?_, rfl, rfl⟩
  rw [alive_eq_of_goodOutcome (ν := ⟨edgeRelay, false⟩) fun _ => (moveCount_edgeRelay _).symm]
  exact Nat.one_pos

/-- **The units between the chamber `false` and its parent**, the root, for the outcome `1`: the
new unit `0` of the first channel of the relay of the edge is assigned to the chamber and the
initial unit is not; by `card_assignedUnits_le` there are at most as many as the load `1` of the
edge, so that new unit is the only one. -/
example : (.new edgeChannel 0 : PlanUnit edgeRoutes (edgeLaws F) edgePlacement 1 2) ∈
      assignedUnits edgeRoutes (edgeLaws F) edgePlacement 2 edgeCounts edgeOutcome
        (.ofChamber le_rfl false) ∧
    UnitId.init 0 1 0 ∉ assignedUnits edgeRoutes (edgeLaws F) edgePlacement 2 edgeCounts
      edgeOutcome (.ofChamber le_rfl false) ∧
    (assignedUnits edgeRoutes (edgeLaws F) edgePlacement 2 edgeCounts edgeOutcome
      (.ofChamber le_rfl false)).card = 1 := by
  refine ⟨new_mem_assignedUnits_edge, init_notMem_assignedUnits, le_antisymm
    ((card_assignedUnits_le _).trans_eq ?_) (card_pos.2 ⟨_, new_mem_assignedUnits_edge⟩)⟩
  simp [Tower.incidentSum, edgeLoads, load_edge edgeOutcome]

/-- At the rate `1`, the units between the chamber `false` and its parent are within
`edgeUnitBound` (`parentUnits_le`). -/
example : (assignedUnits edgeRoutes (edgeLaws F) edgePlacement 2 edgeCounts edgeOutcome
      (.ofChamber le_rfl false)).card ≤ edgeUnitBound (edgeLaws F) 2 2 2 1 :=
  (card_assignedUnits_le _).trans (parentUnits_le edgeStageRate le_rfl false)

/-- **The units in the end**: the initial unit from the party `0` to the party `1` is alive and
lies on the edge, not done, so after all moves it is not current any more
(`unitTarget_eq_done_of_mem_cur`). -/
example : UnitId.init 0 1 0 ∉ (towerPlan edgeRoutes (edgeLaws F) edgePlacement 2 1 2).cur
    edgeCounts edgeOutcome (Fintype.card (Move edgeRoutes edgeBase (edgeLaws F))) := fun hu => by
  have := unitTarget_eq_done_of_mem_cur hu ⟨by decide, by decide⟩
  simp only [unitTarget, initialTarget_edge] at this
  cases this

/-! ### The sizes and the program of the tower with one edge -/

/-- The sizes of the tower with one edge, its routes and its laws are at most `2`. -/
private theorem edgeSize : SizeBound (edgeLaws F) 1 2 2 where
  one_le := by norm_num
  types_le := by norm_num
  places_le := by norm_num
  degree_le := by norm_num
  length_le := by norm_num
  stages_le := by norm_num
  base_le := le_rfl
  card_X_zero_le := le_rfl
  card_kind_le := by simp [unitLaws]
  card_slot_le _ := (rfl : Fintype.card Empty = 0).trans_le (Nat.zero_le 2)

/-- The tree of the tower with one edge has three nodes, the parties of its placement, at most
`3 · 2 ^ 2`. -/
example : Fintype.card edgeTower.Node = 3 ∧ Fintype.card edgeTower.Node ≤ 3 * 2 ^ 2 :=
  ⟨Placement.card_node edgePlacement, card_node_le two_pos (edgeSize (F := ℕ))⟩

/-- A placement of the tower with one edge exists, with one extra party. -/
example : Nonempty (Placement edgeTower edgeBase 1) := by
  simpa [Placement.card_node edgePlacement] using exists_placement edgeTower edgeBase

/-- The plan of the tower with one edge has at most `1092` units, with one initial unit between
two base parties and one unit on every channel: `4` initial units, and at most `17 · 2 ^ 6`
channels (`card_moveChannel_le`). -/
private theorem edge_numUnits_le : numUnits edgeRoutes edgeBase (edgeLaws F) 1 1 ≤ 1092 := by
  have := card_moveChannel_le (R := edgeRoutes) (ch := edgeBase) two_pos (edgeSize (F := F))
  simp only [numUnits]
  omega

/-- The bounds for the program of the plan of the tower with one edge, for `Y = 1100`. -/
private theorem edgeProgramBound : ProgramBound edgeRoutes edgeBase (edgeLaws F) 1 1 1100 where
  base_mul_base_le := by norm_num
  numUnits_le := edge_numUnits_le.trans (by norm_num)
  card_channel_le := (card_moveChannel_le two_pos edgeSize).trans (by norm_num)
  card_move_le := (card_move_le two_pos edgeSize Nat.one_pos).trans (by norm_num)
  card_target_le := (show Fintype.card (Target edgeTower 1 2) = 19 by decide).trans_le
    (by norm_num)
  card_node_le := (card_node_le two_pos (edgeSize (F := F))).trans (by norm_num)
  card_pair_le := (show Fintype.card (Sym2 Unit) = 1 by decide).trans_le (by norm_num)
  card_kind_le := by simp [unitLaws]
  types_le := by norm_num
  endTime_le := by decide
  units_le := by
    have := edge_numUnits_le (F := F)
    simp only [show Fintype.card (Sym2 edgeTower.Fl) = 1 by decide]
    omega

/-- The bounds for the units of the plan of the tower with one edge, for `Y = 1100` and `TM = 0`:
at most `9 · 2 ^ 5` slots and `1092` units. -/
private theorem edgePlanUnitBound : UnitBound edgeRoutes (edgeLaws F) edgePlacement 1 1 1100 0 where
  card_slot_le := (card_moveSlot_le two_pos edgeSize Nat.one_pos).trans (by norm_num)
  card_unit_le := (card_planUnit edgePlacement).trans_le (edge_numUnits_le.trans (by norm_num))
  padding_le := by norm_num

/-- **The program of the plan of the tower with one edge.** From a program that computes the
numbers of initial units and the outcomes, `11 + 8 · 1100` stages of `1100 ^ 12` gates compute the
numbers of the plan, two more the tree for its loads, and nine more its units. -/
example {Inp : Type} {N p c : ℕ} {inp : Fin N → Inp → Fin (1100 ^ 4)} {H : Set (Inp → ℕ)}
    (nI : Inp → Fin 2 → Fin 2 → Fin 2)
    (oI : Inp → (moves edgeRoutes (edgeLaws F) edgePlacement).Channel → Fin 1)
    (hS : SlpN inp (p + c * 1100 ^ 12) H)
    (hi : InputsIn (fun x => initialCounts (nI x))
      (fun x => outcomeOf _ _ edgePlacement (oI x)) H) :
    ∃ H', SlpN inp (p + (c + 11 + 8 * 1100 + 2 + 9) * 1100 ^ 12) H' ∧
      TreeIn Nat.one_pos (fun x => load 2 (initialCounts (nI x))
        (outcomeOf _ _ edgePlacement (oI x))) H' ∧ UnitsIn nI oI 2 0 H' := by
  have hY : StepBase (1100 ^ 4) 1100 := ⟨by norm_num, le_rfl⟩
  obtain ⟨H1, s1, -, f1⟩ := counts_stage hY edgeProgramBound (InputBound.ofPlan nI oI)
    Nat.one_pos hS hi
  obtain ⟨H2, s2, u2, f2⟩ := tree_stage hY edgeProgramBound Nat.one_pos
    (fun x τ => loadGiven_le_numUnits ((InputBound.ofPlan nI oI).initial_le x)
      ((InputBound.ofPlan nI oI).outcome_le x) _ τ) s1 f1.load f1.toChoicesIn
  obtain ⟨H3, s3, u3, f3⟩ := units_stage hY edgeProgramBound edgePlanUnitBound s2 (f1.mono u2)
  exact ⟨H3, s3, ⟨fun P P' => u3 (f2.parent P P'), fun P => u3 (f2.parentUnits P)⟩, f3⟩

/-! ### The rules and the units for an arbitrary tower -/

/-- In the tower plan a slot is given at most `cap` units, if every move uses at most `cap`
units. The bound `hcap` is a hypothesis here. -/
example {T : Tower h b D J r} (R : Routes T m Uu) {ch : Fin A ↪ T.X 0} (FL : VertexLaws F T)
    (Pl : Placement T ch A') (hr : 0 < r) (hb : 0 < b)
    (hcap : ∀ (n : Fin A → Fin A → Fin (U0 + 1)) (o : (moves R FL Pl).Channel → Fin U1) mv,
      moveCount lhat (initialCounts n) (outcomeOf R FL Pl o) mv ≤ cap)
    (n : Fin A → Fin A → Fin (U0 + 1)) (o : (moves R FL Pl).Channel → Fin U1)
    (z : (moves R FL Pl).Slot) : ((towerPlan R FL Pl lhat U0 U1).given n o z).card ≤ cap :=
  have hP := towerPlan_ok hr hb hcap
  (hP.card_given_le n o z).trans (hP.count_le n o z.1)

section

variable {T : Tower h b D J r} {R : Routes T m Uu} {ch : Fin A ↪ T.X 0} {FL : VertexLaws F T}
  {Pl : Placement T ch A'} (n : Fin A → Fin A → Fin (U0 + 1)) (o : (moves R FL Pl).Channel → Fin U1)

/-- An alive unit of a channel that is current after all moves is done: a channel of a law move is
never done. -/
example (l : VertexMove FL) (c : (FL.law l.kind).Channel) (ν : (moves R FL Pl).Channel)
    (hν : moveChannelEquiv R FL Pl ν = ⟨.vertex l, c⟩) (k : Fin U1)
    (hu : (.new ν k : PlanUnit R FL Pl U0 U1) ∈
      (towerPlan R FL Pl lhat U0 U1).cur n o (Fintype.card (Move R ch FL))) :
    ¬ IsAlive R FL Pl lhat n o (.new ν k) := fun ha => by
  have := unitTarget_eq_done_of_mem_cur hu ha
  rw [show unitTarget R FL Pl (.new ν k : PlanUnit R FL Pl U0 U1) =
    (moveChannelEquiv R FL Pl ν).1.target (moveChannelEquiv R FL Pl ν).2 from rfl, hν] at this
  simp [Move.target] at this

/-- The units that a party ever holds, exactly: the initial units of its strings and, for every
end of a channel at it, the outcome of the channel and one more unit. -/
example (p : Fin (A + A')) :
    heldCount R FL Pl n o p =
      (∑ a, ∑ b, if p = Fin.castAdd A' a ∨ p = Fin.castAdd A' b then (n a b : ℕ) else 0) +
        ∑ ν with (ν.1 : ℕ) < Fintype.card (Move R ch FL),
          ∑ d, if (moves R FL Pl).channelParty ν d = p then (o ν : ℕ) + 1 else 0 :=
  Plan.card_filter_holds_seenAt _ p

/-- Possible outcomes are good, in the form of the hypothesis of `Cut.Plan.value_moves`. -/
example {ub : ℕ} (hub : 0 < ub) :
    ∀ n o x, (towerPlan R FL Pl lhat U0 U1).Possible n o ub x →
      (towerPlan R FL Pl lhat U0 U1).Good n o x :=
  fun _ _ _ => towerPlan_good_of_possible hub

/-- For good outcomes, what the party of a node ever holds alone is bounded by the bound for what
it holds and reads. -/
example (hr : 0 < r) (hb : 0 < b) (hh : 0 < h) (hg : ∀ x, (towerPlan R FL Pl lhat U0 U1).Good n o x)
    (hnr : ∀ f : T.Fl, ∃ ν, T.cN ν = f ∨ T.dN ν = f) {Sm : ℕ}
    (hSm : ∀ d, Fintype.card (FL.law d).Slot ≤ Sm) {ℓf : ℕ} (c : T.X J)
    (hini : ∀ a, Tower.Node.ofChamber (Nat.zero_le J) (ch a) = .ofChamber le_rfl c →
      ∑ c', ((n a c' : ℕ) + n c' a) ≤ ℓf) :
    heldCount R FL Pl n o (Pl.party (.ofChamber le_rfl c)) ≤
      (if ∃ a, Tower.Node.ofChamber (Nat.zero_le J) (ch a) = .ofChamber le_rfl c then
        ℓf + 8 * m * lhat else 0) +
        channelEndCount R FL Pl (Pl.party (.ofChamber le_rfl c)) +
        (4 + (2 * Fintype.card T.Nr * FL.lengthBound + 1 + Sm) * Fintype.card FL.Kind) *
          (8 * T.parentUnits (edgeLoads (load lhat (initialCounts n) (outcomeOf R FL Pl o))) J c +
            3 * T.childUnits hh (edgeLoads (load lhat (initialCounts n) (outcomeOf R FL Pl o)))
              J c) :=
  le_self_add.trans (heldCount_add_sum_roleUnits_le hr hb hh hg hnr hSm _ hini)

end

/-! ### Laws at the vertices of other towers -/

/-- The laws at the vertices of the tower with one edge, at the vertices of the tower without
edges: both have one place at a vertex and no near pairs. -/
private abbrev pointLaws (F : Type) [CommSemiring F] : VertexLaws F (pointTower 1) :=
  (edgeLaws F).transfer (pointTower 1) (Equiv.refl _) (Equiv.refl _) fun ν => ν.elim

/-- The transferred laws have the constants of the laws of the tower with one edge. -/
example : (pointLaws F).scale = 1 ∧ (pointLaws F).contraction = 0 := ⟨rfl, rfl⟩

/-- The towers of `SL_h(F₂)` have the same places, near pairs and ends for every `n`, so the laws
at the vertices of one of them are laws at the vertices of every other one. -/
noncomputable example [NeZero h] (h2 : 2 ≤ h) (n n' : ℕ)
    (FL : VertexLaws F (SLTower.tower h n h2)) :
    VertexLaws F (SLTower.tower h n' h2) :=
  FL.transfer _ (Equiv.refl _) (Equiv.refl _) fun _ => rfl

/-- The `6` ordered pairs of different elements of `Fin 3` are twice the `3` unordered pairs off
the diagonal. -/
example : ∑ q : Sym2 (Fin 3), (if q.IsDiag then 0 else 1 : ℕ) = 3 := by
  have h := Fintype.sum_sum_ite_eq_two_nsmul_sum_sym2 fun _ : Sym2 (Fin 3) => (1 : ℕ)
  have h6 : ∑ a : Fin 3, ∑ b : Fin 3, (if a = b then 0 else 1 : ℕ) = 6 := by decide
  rw [h6, smul_eq_mul] at h
  omega

end CslibFrontierTests.SeparationTowerPlan
