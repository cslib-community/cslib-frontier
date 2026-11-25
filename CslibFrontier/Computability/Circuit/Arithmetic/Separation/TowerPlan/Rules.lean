/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.PlayMoves
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.Holders
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.Plan
import Mathlib.Order.Bounds.Basic

/-!
# The tower plan obeys the rules

The tower plan of [AnthropicVPVNP2026] (proof of Theorem H.2; module `Nc.Tow.Ok`) obeys the rules
of a plan (`Cut.Plan.Ok`): what a move is given, the number of units that it uses and which of
its outcomes are good depend on the outcomes of earlier moves only; only current units are given,
each at one slot, between the parties at the ends of the slot; and a slot is given at most as
many units as its move uses.

## Main results

* `towerPlan_ok`: the tower plan obeys the rules, for every bound `cap` on the numbers of units
  of its moves.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Theorem H.2 (proof); module `Nc.Tow.Ok`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.TowerPlan

open Finset Cslib.CoveringTower Cut

variable {F : Type*} [CommSemiring F] {h b D J r m Uu A A' U0 U1 : ℕ} {T : Tower h b D J r}
  {R : Routes T m Uu} {ch : Fin A ↪ T.X 0} {FL : VertexLaws F T} {Pl : Placement T ch A'}
  {lhat : ℕ}

/-- Relays that are used are determined by their inputs. -/
private theorem Relay.eq_of_input_eq {L : Target T m A → ℕ} {x x' : Relay T m A}
    (hx : x.Occurs R ch) (hx' : x'.Occurs R ch) (ha : x.Active L) (ha' : x'.Active L)
    (he : x.input = x'.input) : x = x' := by
  rcases x with ⟨a, c, γ, s⟩ | ⟨j, i, e⟩ | ⟨j, e, s⟩ | e <;>
    rcases x' with ⟨a', c', γ', s'⟩ | ⟨j', i', e'⟩ | ⟨j', e', s'⟩ | e' <;>
    simp only [Relay.input] at he <;> (try split_ifs at he) <;>
    grind [Relay.Active, Relay.Occurs, Tower.IsChosenType, IsLeast.unique, Fin.castSucc_inj,
      Fin.castSucc_ne_last]

private theorem slotRank_inj {d : FL.Kind} {e e' : (FL.law d).Slot}
    (hp : FL.slotPair d e = FL.slotPair d e') (hs : FL.slotRank d e = FL.slotRank d e') :
    e = e' :=
  rk_inj (fun _ _ hab => (Fintype.equivFin (FL.law d).Slot).injective (Fin.ext hab))
    (mem_univ _) (mem_univ _) hp hs

section Plan

variable {n : Fin A → Fin A → Fin (U0 + 1)} {o o' : (moves R FL Pl).Channel → Fin U1}

private theorem slotInput_ne_done (z : MoveSlot R ch FL) : slotInput R FL z ≠ .done := by
  rcases z with ⟨⟨x, hx⟩ | l, e⟩ <;> simp [slotInput]

private theorem time_slotInput_le (z : MoveSlot R ch FL) :
    (slotInput R FL z).time ≤ z.1.time := by
  rcases z with ⟨⟨x, hx⟩ | l, e⟩
  · exact x.time_input_le
  · exact le_rfl

/-- A unit is given at one slot at most. -/
private theorem givenUnits_unique {z z' : MoveSlot R ch FL} {u : PlanUnit R FL Pl U0 U1}
    (hu : u ∈ givenUnits R FL Pl lhat n o z) (hu' : u ∈ givenUnits R FL Pl lhat n o z') :
    z = z' := by
  rcases z with ⟨⟨x, hx⟩ | l, e⟩ <;> rcases z' with ⟨⟨x', hx'⟩ | l', e'⟩
  · obtain ⟨h1, -, h2⟩ := mem_givenUnits_relay.1 hu
    obtain ⟨h1', -, h2'⟩ := mem_givenUnits_relay.1 hu'
    obtain rfl := Relay.eq_of_input_eq hx hx' h1 h1' (h2.symm.trans h2')
    rfl
  · exact absurd ((mem_givenUnits_relay.1 hu).2.2.symm.trans (mem_givenUnits_vertex.1 hu').2.2.1)
      Relay.input_ne_segment
  · exact absurd ((mem_givenUnits_relay.1 hu').2.2.symm.trans (mem_givenUnits_vertex.1 hu).2.2.1)
      Relay.input_ne_segment
  · obtain ⟨h1, -, h2, h3, h4⟩ := mem_givenUnits_vertex.1 hu
    obtain ⟨h1', -, h2', h3', h4'⟩ := mem_givenUnits_vertex.1 hu'
    obtain ⟨j, i, ω, d⟩ := l
    obtain ⟨j', i', ω', d'⟩ := l'
    obtain ⟨rfl, rfl, hω, hq⟩ := Target.segment.inj (h2.symm.trans h2')
    obtain rfl := eq_of_heq hω
    obtain rfl : d = d' := VertexMove.kind_eq_of_isPicked (l := ⟨j, i, ω, d⟩) h1 h1'
    obtain rfl := slotRank_inj hq
      ((Nat.div_eq_of_lt_le h3 h4).symm.trans (Nat.div_eq_of_lt_le h3' h4'))
    rfl

/-- The holders of a unit are the parties of the nodes of its target. -/
private theorem holder_eq {u : PlanUnit R FL Pl U0 U1} (hd : unitTarget R FL Pl u ≠ .done) :
    s(UnitId.holder (moves R FL Pl).channelParty u false,
      UnitId.holder (moves R FL Pl).channelParty u true) =
      ((unitTarget R FL Pl u).holders R ch).map Pl.party := by
  cases u with
  | init a c k =>
    rw [unitTarget, holders_initialTarget hd, initialHolders, Sym2.map_mk]
    simp only [Pl.party_base]
    rfl
  | new ν k =>
    rw [unitTarget, holders_target _ hd]
    rfl

/-- The parties at the ends of a slot are the parties of the nodes of its input. -/
private theorem slotParty_eq (z : (moves R FL Pl).Slot) :
    s((moves R FL Pl).slotParty z false, (moves R FL Pl).slotParty z true) =
      ((slotInput R FL (moveSlotEquiv R FL Pl z)).holders R ch).map Pl.party := by
  rw [slotParty_moves, slotParty_moves]
  generalize moveSlotEquiv R FL Pl z = w
  rcases w with ⟨⟨x, hx⟩ | l, e⟩
  · have h1 : x.input.holders R ch = s(x.party R ch .source, x.party R ch .sink) := by
      rcases x with ⟨a, c, γ, s⟩ | ⟨j, i, e⟩ | ⟨j, e, s⟩ | e
      · rfl
      · rfl
      · simp only [Relay.input]
        split_ifs with hs
        · subst hs; rfl
        · rfl
      · rfl
    rw [slotInput, h1]
    rfl
  · rfl

section Causal

variable {t : ℕ}

private theorem outcomeOf_congr {p : Move R ch FL → Prop}
    (ho : ∀ ν : (moves R FL Pl).Channel, p (moveOrder R ch FL ν.1) → o ν = o' ν)
    (ν : MoveChannel R ch FL) (hν : p ν.1) : outcomeOf R FL Pl o ν = outcomeOf R FL Pl o' ν :=
  congrArg Fin.val (ho _ (by rwa [← fst_moveChannelEquiv (Pl := Pl), Equiv.apply_symm_apply]))

private theorem isAlive_congr (hr : 0 < r) (hb : 0 < b)
    (hag : ∀ ν : MoveChannel R ch FL, ν.1.time < t →
      outcomeOf R FL Pl o ν = outcomeOf R FL Pl o' ν)
    {u : PlanUnit R FL Pl U0 U1} (hu : (unitTarget R FL Pl u).time ≤ t) :
    IsAlive R FL Pl lhat n o u ↔ IsAlive R FL Pl lhat n o' u := by
  cases u with
  | init a c k => exact Iff.rfl
  | new ν k =>
    have h1 : (moveChannelEquiv R FL Pl ν).1.time < t :=
      ((moveChannelEquiv R FL Pl ν).1.time_lt_time_target _).trans_le hu
    simp only [IsAlive, alive, moveCount_congr hr hb fun ν' hν' => hag ν' (hν'.trans h1),
      aliveGiven_congr fun ν' hν' => hag ν' (hν' ▸ h1)]

private theorem givenUnits_congr (hr : 0 < r) (hb : 0 < b) (z : MoveSlot R ch FL)
    (hag : ∀ ν : MoveChannel R ch FL, ν.1.time < z.1.time →
      outcomeOf R FL Pl o ν = outcomeOf R FL Pl o' ν) :
    (givenUnits R FL Pl lhat n o z : Finset (PlanUnit R FL Pl U0 U1)) =
      givenUnits R FL Pl lhat n o' z := by
  have hal (v : PlanUnit R FL Pl U0 U1) (hv : unitTarget R FL Pl v = slotInput R FL z) :
      IsAlive R FL Pl lhat n o v ↔ IsAlive R FL Pl lhat n o' v :=
    isAlive_congr hr hb hag (hv ▸ time_slotInput_le z)
  ext u
  rcases z with ⟨⟨x, hx⟩ | l, e⟩
  · refine mem_givenUnits_relay.trans (Iff.trans ?_ mem_givenUnits_relay.symm)
    rw [Relay.active_congr fun τ hτ => load_congr hr hb hτ hag]
    exact and_congr_right fun _ => and_congr_left fun hu => hal u hu
  · have hrk (v : PlanUnit R FL Pl U0 U1)
        (hv : unitTarget R FL Pl v = slotInput R FL ⟨.vertex l, e⟩) :
        unitRank R FL Pl lhat n o v = unitRank R FL Pl lhat n o' v :=
      rk_congr fun w hw => by simpa using hal w (hw.trans hv)
    refine mem_givenUnits_vertex.trans (Iff.trans ?_ mem_givenUnits_vertex.symm)
    rw [VertexMove.isPicked_congr fun q => load_congr hr hb le_rfl hag, moveCount_congr hr hb hag]
    exact and_congr_right fun _ => ⟨fun ⟨h1, h2, h3⟩ => ⟨(hal u h2).1 h1, h2, hrk u h2 ▸ h3⟩,
      fun ⟨h1, h2, h3⟩ => ⟨(hal u h2).2 h1, h2, (hrk u h2).symm ▸ h3⟩⟩

end Causal

/-- Units that are given are current. -/
private theorem givenUnits_subset_cur {z : (moves R FL Pl).Slot} {u : PlanUnit R FL Pl U0 U1}
    (hu : u ∈ givenUnits R FL Pl lhat n o (moveSlotEquiv R FL Pl z)) :
    u ∈ (towerPlan R FL Pl lhat U0 U1).cur n o z.1 := by
  obtain ⟨h1, h2⟩ := isAlive_of_mem_givenUnits hu
  refine Plan.mem_cur.2 ⟨?_, fun z' hz' hu' => ?_⟩
  · cases u with
    | init a c k => exact Plan.init_mem_seenAt.2 h1.2
    | new ν k =>
      have h3 := (((moveChannelEquiv R FL Pl ν).1.time_lt_time_target _).trans_le
        (h2 ▸ time_slotInput_le _))
      have h4 : alive lhat (initialCounts n) (outcomeOf R FL Pl o)
          (moveChannelEquiv R FL Pl ν) ≤ outcomeOf R FL Pl o (moveChannelEquiv R FL Pl ν) :=
        aliveGiven_le _ _
      have h5 : (k : ℕ) < alive lhat (initialCounts n) (outcomeOf R FL Pl o)
        (moveChannelEquiv R FL Pl ν) := h1
      have h6 : outcomeOf R FL Pl o (moveChannelEquiv R FL Pl ν) = (o ν : ℕ) := by
        simp [outcomeOf]
      exact Plan.new_mem_seenAt.2 ⟨lt_of_time_moveOrder_lt h3, Fin.le_def.2 (by omega)⟩
  · obtain rfl := (moveSlotEquiv R FL Pl).injective (givenUnits_unique hu hu')
    exact lt_irrefl _ hz'

/-- **The tower plan obeys the rules.** The bound `cap` for the numbers of units of the moves is
a hypothesis. -/
theorem towerPlan_ok (hr : 0 < r) (hb : 0 < b) {cap : ℕ}
    (hcap : ∀ (n : Fin A → Fin A → Fin (U0 + 1)) (o : (moves R FL Pl).Channel → Fin U1) mv,
      moveCount lhat (initialCounts n) (outcomeOf R FL Pl o) mv ≤ cap) :
    (towerPlan R FL Pl lhat U0 U1).Ok cap where
  given_congr n o o' z ho := givenUnits_congr hr hb _ (outcomeOf_congr
    (p := (·.time < (moveOrder R ch FL z.1).time)) fun ν hν => ho ν (lt_of_time_moveOrder_lt hν))
  count_congr n o o' x ho := moveCount_congr hr hb (outcomeOf_congr
    (p := (·.time < (moveOrder R ch FL x).time)) fun ν hν => ho ν (lt_of_time_moveOrder_lt hν))
  good_congr n o o' x ho := goodOutcome_congr hr hb
    (outcomeOf_congr (p := (·.time < (moveOrder R ch FL x).time)) fun ν hν =>
      ho ν (lt_of_time_moveOrder_lt hν).le)
    (outcomeOf_congr (p := (· = moveOrder R ch FL x)) fun ν hν =>
      ho ν ((moveOrder R ch FL).injective hν).le)
  given_subset n o z u hu := givenUnits_subset_cur hu
  holder_given n o z u hu := by
    have h2 := (isAlive_of_mem_givenUnits hu).2
    have h3 := holder_eq (u := u) (h2 ▸ slotInput_ne_done _)
    rw [h2, ← slotParty_eq] at h3
    rcases Sym2.eq_iff.1 h3 with h | h
    · exact ⟨false, by rintro (_ | _) <;> simp [h]⟩
    · exact ⟨true, by rintro (_ | _) <;> simp [h]⟩
  given_disjoint n o x e e' hee := disjoint_left.2 fun u hu hu' => hee (by
    simpa using (moveSlotEquiv R FL Pl).injective (givenUnits_unique hu hu'))
  card_given_le n o z := card_givenUnits_le _
  count_le n o x := hcap n o _

end Plan

end Cslib.Circuits.Arithmetic.Separation.TowerPlan
