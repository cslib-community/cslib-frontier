/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.Rules
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
* `towerPlan_ok` for an arbitrary tower, under its hypotheses: a slot is given at most `cap`
  units. -/

set_option linter.privateModule false

namespace CslibFrontierTests.SeparationTowerPlan

open Finset Cslib Cslib.CoveringTower Cslib.Circuits.Arithmetic.Separation
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
example : Node.ofChamber le_rfl (T.e0 e) ≠ Node.ofChamber le_rfl (T.e1 e) := fun he =>
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
of its own. -/
@[reducible] private def edgeTower : Tower 1 1 1 0 1 where
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

/-- The first step from `false` to `true` arrives. -/
private theorem not_one_lt_pl (γ : Bool) : ¬ 1 < edgeRoutes.pl false true γ := fun h1 => by
  obtain ⟨_, -, -, hne⟩ := edgeRoutes.exists_edge false true γ (s := 0) (by omega)
  have := edgeRoutes.pn_ne false true γ h1
  rw [edgeRoutes.pn_zero] at hne
  cases h : edgeRoutes.pn false true γ 1 <;> simp_all

/-- The unit from the party `0` to the party `1` goes over the edge, at the last stage. -/
private theorem initialTarget_edge (k : ℕ) :
    initialTarget edgeRoutes edgeBase 0 1 k = .edge (Fin.last 0) () := by
  have hpl := edgeRoutes.pl_pos Bool.false_ne_true (batchChamber edgeBase 0 k)
  obtain ⟨e, he, -⟩ := edgeRoutes.exists_edge false true (batchChamber edgeBase 0 k) hpl
  have h0 : ¬ (0 < 2 * 1 ∧
      1 < edgeRoutes.pl (edgeBase 0) (edgeBase 1) (batchChamber edgeBase 0 k)) :=
    fun h => not_one_lt_pl _ h.2
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

/-- The plan obeys the rules, and the unit from the party `0` to the party `1` is given at the
slot of the relay of the edge: so that slot joins the parties `0` and `1`. -/
example : s((moves edgeRoutes (edgeLaws F) edgePlacement).slotParty
      ((moveSlotEquiv _ _ edgePlacement).symm ⟨edgeRelay, ()⟩) false,
    (moves edgeRoutes (edgeLaws F) edgePlacement).slotParty
      ((moveSlotEquiv _ _ edgePlacement).symm ⟨edgeRelay, ()⟩) true) = s(0, 1) := by
  obtain ⟨d, hd⟩ := (towerPlan_ok Nat.one_pos Nat.one_pos
    (moveCount_le (F := F) 2 1 1)).holder_given edgeCounts (fun _ => 0)
    ((moveSlotEquiv _ _ edgePlacement).symm ⟨edgeRelay, ()⟩) (.init 0 1 0)
    (by simpa [towerPlan] using init_mem_givenUnits (F := F) (U1 := 1) (fun _ => 0))
  have h0 := hd false
  have h1 := hd true
  cases d <;> simp only [UnitId.holder, Bool.xor_false, Bool.xor_true, Bool.not_false,
    Bool.not_true, Bool.cond_false, Bool.cond_true] at h0 h1 <;> rw [← h0, ← h1] <;> decide

/-! ### The rules for an arbitrary tower -/

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

end CslibFrontierTests.SeparationTowerPlan
