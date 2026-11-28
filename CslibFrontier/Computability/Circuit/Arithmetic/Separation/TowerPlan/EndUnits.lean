/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.Holders
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.Plan
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.PlayMoves
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.Norms
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.StartLoads
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.FinCases

/-!
# The tower plan: the units in the end

After all moves of the tower plan of [AnthropicVPVNP2026] (proof of Theorem H.2; modules
`Nc.Tow.EndA`, `Nc.Tow.EndB`, `Nc.Tow.EndC`), every alive unit whose target is not done has been
given at a slot, so the alive current units are done (`unitTarget_eq_done_of_mem_cur`). A channel
of a relay that uses units and whose units are done joins a chamber, the node below the parent on
it (`Relay.child`), and the parent of that chamber in the tree
(`Cslib.CoveringTower.Tower.Node.parent`): `channelHolders_of_target_eq_done`. The alive units of
such channels at a node (`assignedUnits`) are at most the units between the chamber and its parent
(`card_assignedUnits_le`). The last unit of every channel is never moved again (`deadUnits`).
Possible outcomes are good (`towerPlan_good_of_possible`), and for good outcomes all units of a
channel but the last are alive (`alive_eq_of_goodOutcome`).

## Main definitions

* `Relay.child`: the node below the parent on a channel of a relay.
* `IsChild`, `assignedUnits`: the channels whose units are between a node and its parent, and
  their alive units.
* `deadUnits`: the last unit of every channel.

## Main results

* `unitTarget_eq_done_of_mem_cur`: the alive units in the end are done.
* `channelHolders_of_target_eq_done`: a done channel of a relay joins a chamber and its parent.
* `card_assignedUnits_le`: the units between a node and its parent.
* `towerPlan_good_of_possible`, `alive_eq_of_goodOutcome`: possible outcomes are good, and the
  alive units of a good outcome.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Section H.2 (law moves), p. 45, Theorem H.2(b), p. 46, and its proof ("One stage" and
  "Bounds", p. 47); modules `Nc.Tow.EndA`, `Nc.Tow.EndB`, `Nc.Tow.EndC`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.TowerPlan

open Finset Cslib.CoveringTower Cut

variable {F : Type*} [CommSemiring F] {h b D J r m Uu A A' U0 U1 : ℕ} {T : Tower h b D J r}
  {R : Routes T m Uu} {ch : Fin A ↪ T.X 0} {FL : VertexLaws F T} {Pl : Placement T ch A'}
  {lhat : ℕ}

/-! ### The tree -/

/-- The node below the parent on the channel `β` of a relay: the party at its outer end, the
source for `false` and the sink for `true`. -/
@[expose] def Relay.child (R : Routes T m Uu) (ch : Fin A ↪ T.X 0) (x : Relay T m A) (β : Bool) :
    T.Node :=
  x.party R ch (bif β then .sink else .source)

/-- The channel `ν` is a child channel of the node `P`: a channel of a relay whose units are done
and whose node below the parent is `P`. -/
@[expose] def IsChild (P : T.Node) : MoveChannel R ch FL → Prop
  | ⟨.relay x _, β⟩ => x.target R ch β = .done ∧ x.child R ch β = P
  | ⟨.vertex _, _⟩ => False

instance (P : T.Node) : DecidablePred (IsChild P : MoveChannel R ch FL → Prop)
  | ⟨.relay x _, β⟩ => inferInstanceAs (Decidable (x.target R ch β = .done ∧ x.child R ch β = P))
  | ⟨.vertex _, _⟩ => inferInstanceAs (Decidable False)

section Channels

variable {n : Fin A → Fin A → ℕ} {o : MoveChannel R ch FL → ℕ}

/-- The channels of a relay of a route are never done. -/
private theorem start_target_ne_done {a c : Fin A} {γ : T.X 0} {s : Fin (2 * m)}
    (hx : (Relay.start a c γ s).Occurs R ch) (β : Bool) :
    (Relay.start a c γ s : Relay T m A).target R ch β ≠ .done := by
  have hs := hx.2
  cases β
  · exact stepTarget_ne_done (by omega)
  · simp only [Relay.target]
    split_ifs
    · simp
    · exact stepTarget_ne_done hs

/-- **A done channel of a relay joins a chamber and its parent** ([AnthropicVPVNP2026],
Theorem H.2(b), p. 46): if a relay of the plan uses units and its channel `β` is done, the
channel joins the node below the parent on it and the parent of that node. -/
theorem channelHolders_of_target_eq_done (hh : 0 < h) {x : Relay T m A} (hx : x.Occurs R ch)
    {β : Bool} (hd : x.target R ch β = .done) (hne : moveCount lhat n o (.relay x hx) ≠ 0) :
    channelHolders (⟨.relay x hx, β⟩ : MoveChannel R ch FL) =
      s(x.child R ch β, (x.child R ch β).parent hh (edgeLoads (load lhat n o))) := by
  set L := edgeLoads (load lhat n o)
  have hpar {j : Fin J} (c : T.X j) : (Tower.Node.ofChamber j.isLt.le c).parent hh L =
      .ofChamber j.isLt (T.parentChamber hh L c) := dite_eq_left j.isLt
  rcases x with ⟨a, c, γ, s⟩ | ⟨j, i, e⟩ | ⟨j, e, s⟩ | e
  · exact absurd hd (start_target_ne_done hx β)
  · obtain rfl : i = T.chosenType hh L j := Decidable.byContradiction fun hi => hne <|
      (moveCount_eq _).trans (ite_eq_right fun h => hi ((Tower.isChosenType_iff hh).1 h))
    have h1 : T.vx (T.chosenType hh L j) (T.e0 e) = T.vx (T.chosenType hh L j) (T.e1 e) :=
      (T.nr_vx0 j.isLt.le _ ⟨e, hx⟩).trans (T.nr_vx1 j.isLt.le _ ⟨e, hx⟩).symm
    cases β <;> simp [channelHolders, Relay.child, Relay.party, Move.party, Move.law, relayLaw,
      relayChannelEnd, RelayRole.elim, hpar, Tower.parentChamber, Tower.hostOf, h1, Sym2.eq_swap]
  · have ht : T.ty e = T.chosenType hh L j :=
      Decidable.byContradiction fun ht => hne <| Nat.eq_zero_of_le_zero <|
        (moveCount_middle_le hx).trans_eq
          (ite_eq_right fun h => ht ((Tower.isChosenType_iff hh).1 h))
    cases β <;> fin_cases s <;> simp only [Relay.target] at hd <;> (try split_ifs at hd) <;>
      simp_all [channelHolders, Relay.child, Relay.party, Move.party, Move.law, relayLaw,
        relayChannelEnd, RelayRole.elim, Tower.parentChamber, Sym2.eq_swap]
  · have hJ (c : T.X J) : (Tower.Node.ofChamber le_rfl c).parent hh L = .root :=
      dite_eq_right (Nat.not_succ_le_self J)
    cases β <;> simp [channelHolders, Relay.child, Relay.party, Move.party, Move.law, relayLaw,
      relayChannelEnd, RelayRole.elim, hJ, Sym2.eq_swap]

/-- The done channels of the relays of an edge at one end carry at most the units on the edge:
the inner relay of the chosen type if the edge is of another type, and else the last relay of the
way of the edge. -/
private theorem sum_done_le_load (j : Fin J) (e : T.Ed j) (β : Bool) :
    (∑ i, relayAlive lhat n o (.inner j i e) β) + ∑ s, (if (Relay.middle j e s : Relay T m A).target
      R ch β = .done then relayAlive lhat n o (.middle j e s) β else 0) ≤
      edgeLoads (load lhat n o) j e := by
  have hh := (T.ty e).pos
  set i₀ := T.chosenType hh (edgeLoads (load lhat n o)) j
  have hI : ∑ i, relayAlive lhat n o (.inner j i e) β ≤
      if T.IsChosenType (edgeLoads (load lhat n o) j) (T.ty e) then 0
      else edgeLoads (load lhat n o) j e := by
    rw [sum_eq_single i₀ (fun i _ hi => Nat.eq_zero_of_le_zero
      ((relayAlive_inner_le j i e β).trans_eq
        (ite_eq_right fun h => hi ((Tower.isChosenType_iff hh).1 h)))) (by simp)]
    split_ifs with ht
    · exact (relayAlive_of_not_occurs (lhat := lhat) (n := n) (o := o)
        (fun hx : (Relay.inner j i₀ e).Occurs R ch => hx ((Tower.isChosenType_iff hh).1 ht)) β).le
    · exact (relayAlive_inner_le j i₀ e β).trans (by split_ifs <;> simp)
  have hM (s : Fin 4) := relayAlive_middle_le (lhat := lhat) (n := n) (o := o) (R := R) (ch := ch)
    j e s β
  have h3 : T.π (T.e1 e) = T.hostOf (T.ty e) (T.e1 e) →
      relayAlive lhat n o (.middle j e 3) β = 0 := fun hq =>
    relayAlive_of_not_occurs (fun hx : (Relay.middle j e 3).Occurs R ch => hx.2 rfl hq) β
  rw [Fin.sum_univ_four]
  cases β <;> simp only [Relay.target, Fin.isValue, Matrix.cons_val] <;> split_ifs at * <;>
    simp_all [hM 0, hM 2, hM 3]

/-- The done channels of the relays of an edge at the node `P`: at most the units on the edge if an
end of the edge is `P`, and none otherwise. -/
private theorem sum_done_le (P : T.Node) (j : Fin J) (e : T.Ed j) (β : Bool) :
    (∑ i, if (Relay.inner j i e : Relay T m A).target R ch β = .done ∧
      (Relay.inner j i e).child R ch β = P then relayAlive lhat n o (.inner j i e) β else 0) +
    ∑ s, (if (Relay.middle j e s : Relay T m A).target R ch β = .done ∧
      (Relay.middle j e s).child R ch β = P then relayAlive lhat n o (.middle j e s) β else 0) ≤
      if Tower.Node.ofChamber j.isLt.le (bif β then T.e1 e else T.e0 e) = P then
        edgeLoads (load lhat n o) j e else 0 := by
  have hI (i : Fin h) : (Relay.inner j i e : Relay T m A).child R ch β =
      Tower.Node.ofChamber j.isLt.le (bif β then T.e1 e else T.e0 e) := by
    cases β <;> rfl
  have hM (s : Fin 4) : (Relay.middle j e s : Relay T m A).target R ch β = .done →
      (Relay.middle j e s).child R ch β =
        Tower.Node.ofChamber j.isLt.le (bif β then T.e1 e else T.e0 e) := by
    cases β <;> fin_cases s <;> simp [Relay.target, Relay.child, Relay.party, RelayRole.elim]
  split_ifs with hP
  · refine (add_le_add (sum_le_sum fun i _ => by split_ifs <;> simp)
      (sum_le_sum fun s _ => by split_ifs <;> simp_all)).trans (sum_done_le_load j e β)
  · exact Nat.le_zero.2 (Nat.add_eq_zero_iff.2 ⟨sum_eq_zero fun i _ => ite_eq_right fun h =>
      hP (h.2 ▸ hI i).symm, sum_eq_zero fun s _ => ite_eq_right fun h =>
        hP ((hM s h.1).symm.trans h.2)⟩)

/-- The alive units of the child channels of a node are at most the units between the node and
its parent. -/
private theorem sum_isChild_le (P : T.Node) :
    ∑ ν : MoveChannel R ch FL, (if IsChild P ν then alive lhat n o ν else 0) ≤
      P.lift (T.parentUnits (edgeLoads (load lhat n o))) 0 := by
  have h1 : ∑ ν : MoveChannel R ch FL, (if IsChild P ν then alive lhat n o ν else 0) =
      ∑ x, ∑ β, if x.target R ch β = .done ∧ x.child R ch β = P then relayAlive lhat n o x β
        else 0 := by
    rw [Fintype.sum_sigma, Move.sum_eq, sum_eq_zero (s := univ (α := VertexMove FL))
      fun l _ => sum_eq_zero fun c _ => ite_eq_right fun h => h.elim, add_zero]
    refine sum_congr rfl fun x _ => ?_
    by_cases hx : x.Occurs R ch
    · rw [dite_eq_left hx]
      exact sum_congr rfl fun β _ => if_congr Iff.rfl (relayAlive_of_occurs hx β).symm rfl
    · simp [hx, relayAlive_of_not_occurs hx]
  have hS : ∑ a, ∑ c, ∑ γ, ∑ s, ∑ β, (if (Relay.start a c γ s : Relay T m A).target R ch β =
      .done ∧ (Relay.start a c γ s).child R ch β = P then
        relayAlive lhat n o (.start a c γ s) β else 0) = 0 :=
    sum_eq_zero fun a _ => sum_eq_zero fun c _ => sum_eq_zero fun γ _ => sum_eq_zero fun s _ =>
      sum_eq_zero fun β _ => by
        by_cases hx : (Relay.start a c γ s).Occurs R ch
        · exact ite_eq_right fun h => start_target_ne_done hx β h.1
        · simp [relayAlive_of_not_occurs hx]
  have hIM (j : Fin J) : (∑ i, ∑ e, ∑ β, if (Relay.inner j i e : Relay T m A).target R ch β =
      .done ∧ (Relay.inner j i e).child R ch β = P then
        relayAlive lhat n o (.inner j i e) β else 0) +
      (∑ e, ∑ s, ∑ β, if (Relay.middle j e s : Relay T m A).target R ch β = .done ∧
        (Relay.middle j e s).child R ch β = P then relayAlive lhat n o (.middle j e s) β else 0) ≤
      ∑ c : T.X j, if Tower.Node.ofChamber j.isLt.le c = P then
        T.parentUnits (edgeLoads (load lhat n o)) j c else 0 := by
    rw [Tower.sum_ite_incidentSum, sum_comm, ← sum_add_distrib]
    refine sum_le_sum fun e _ => (congrArg₂ (· + ·) sum_comm sum_comm).trans_le ?_
    rw [← sum_add_distrib]
    exact (sum_le_sum fun β _ => sum_done_le P j e β).trans_eq
      (by simp only [Fintype.sum_bool, Bool.cond_false, Bool.cond_true, add_comm])
  have hF : ∑ e : T.Ed J, ∑ β, (if (Relay.final e : Relay T m A).target R ch β = .done ∧
      (Relay.final e).child R ch β = P then relayAlive lhat n o (.final e) β else 0) ≤
      ∑ c : T.X J, if Tower.Node.ofChamber le_rfl c = P then
        T.parentUnits (edgeLoads (load lhat n o)) J c else 0 := by
    rw [Tower.sum_ite_incidentSum]
    refine sum_le_sum fun e _ => ?_
    have h0 := relayAlive_final_le (lhat := lhat) (n := n) (o := o) (R := R) (ch := ch) e false
    have h1 := relayAlive_final_le (lhat := lhat) (n := n) (o := o) (R := R) (ch := ch) e true
    simp only [Fintype.sum_bool, Relay.target, Relay.child, Relay.party, RelayRole.elim, true_and,
      Bool.cond_true, Bool.cond_false]
    split_ifs <;> omega
  have hA := Tower.Node.sum_ofChamber_castSucc (T.parentUnits (edgeLoads (load lhat n o))) P
  rw [h1, Relay.sum_eq, hS, zero_add, ← add_assoc, ← sum_add_distrib]
  exact (add_le_add (sum_le_sum fun j _ => hIM j) hF).trans_eq hA

end Channels

/-! ### The current units in the end -/

/-- The target of a channel of a relay of the plan that is a relay is a relay of the plan that is
used and that is given the units with its own target. -/
private theorem Relay.occurs_of_target_eq_relay {x y : Relay T m A} (hx : x.Occurs R ch)
    {d : Bool} (h : x.target R ch d = .relay y) (L : Target T m A → ℕ) :
    y.Occurs R ch ∧ y.Active L ∧ y.input = .relay y := by
  rcases x with ⟨a, c, γ, s⟩ | ⟨j, i, e⟩ | ⟨j, e, s⟩ | e <;> cases d <;>
    (try fin_cases s) <;> simp only [Relay.target] at h <;> (try split_ifs at h) <;>
    first
    | (cases h; simp_all [Relay.Occurs, Relay.Active, Relay.input])
    | simp_all

/-- The target of an initial unit that is a relay is a relay of the plan that is used and that is
given the units with its own target. -/
private theorem occurs_of_initialTarget_eq_relay {a c : Fin A} {k : ℕ} {y : Relay T m A}
    (h : initialTarget R ch a c k = .relay y) (L : Target T m A → ℕ) :
    y.Occurs R ch ∧ y.Active L ∧ y.input = .relay y := by
  unfold initialTarget at h
  split_ifs at h with hac hs
  · cases h
    exact ⟨⟨hac, hs.2⟩, trivial, rfl⟩
  · simp at h

/-- The end segments of the outer steps of the way of an edge join different places. -/
private theorem not_isDiag_segment {j : ℕ} (hj : j < J) {i : Fin h} {c : T.X j}
    (hc : T.hostOf i c ≠ T.π c) : ¬ (s(T.co i (T.hostOf i c), T.co i c) : Sym2 T.Fl).IsDiag :=
  fun hd => hc ((T.vx_co hj i).1 (Prod.ext (by simp [T.host_vx hj, T.π_vx hj])
    (by simpa [T.π_co hj] using Sym2.mk_isDiag_iff.1 hd)))

variable {n : Fin A → Fin A → Fin (U0 + 1)} {o : (moves R FL Pl).Channel → Fin U1}

/-- An alive unit whose target is not done is given at a slot. -/
private theorem exists_mem_givenUnits {u : PlanUnit R FL Pl U0 U1}
    (hu : IsAlive R FL Pl lhat n o u) (hd : unitTarget R FL Pl u ≠ .done) :
    ∃ z : MoveSlot R ch FL, u ∈ givenUnits R FL Pl lhat n o z := by
  set L := load lhat (initialCounts n) (outcomeOf R FL Pl o)
  have relay {x : Relay T m A} (hx : x.Occurs R ch) (ha : x.Active L)
      (ht : unitTarget R FL Pl u = x.input) :
      ∃ z : MoveSlot R ch FL, u ∈ givenUnits R FL Pl lhat n o z :=
    ⟨⟨.relay x hx, ()⟩, mem_givenUnits_relay.2 ⟨ha, hu, ht⟩⟩
  rcases hτ : unitTarget R FL Pl u with _ | ⟨j, e⟩ | y | ⟨j, i, ω, q⟩
  · exact absurd hτ hd
  · have hh := (T.ty e).pos
    revert e
    refine Fin.lastCases (fun e hτ => relay (x := .final e) trivial trivial hτ) (fun j e hτ => ?_) j
    have hi := Tower.isChosenType_chosenType hh (edgeLoads L) j
    by_cases ht : T.ty e = T.chosenType hh (edgeLoads L) j
    · exact relay (x := .middle j e 0)
        ⟨fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
        (fun _ => ht ▸ hi) (by simp [hτ, Relay.input])
    · exact relay (x := .inner j _ e) ht hi hτ
  · obtain ⟨hy₁, hy₂, hy₃⟩ : y.Occurs R ch ∧ y.Active L ∧ y.input = .relay y := by
      cases u with
      | init a c k => exact occurs_of_initialTarget_eq_relay hτ L
      | new ν k =>
        rcases hw : moveChannelEquiv R FL Pl ν with ⟨⟨x, hx⟩ | l, d⟩ <;> rw [unitTarget, hw] at hτ
        · exact Relay.occurs_of_target_eq_relay hx hτ L
        · cases hτ
    exact relay hy₁ hy₂ (hτ.trans hy₃.symm)
  · have hq : ¬ q.IsDiag := by
      cases u with
      | init a c k =>
        simp only [unitTarget, initialTarget] at hτ
        split_ifs at hτ
        simp at hτ
      | new ν k =>
        rcases hw : moveChannelEquiv R FL Pl ν with ⟨⟨x, hx⟩ | l, d⟩ <;> rw [unitTarget, hw] at hτ
        · obtain ⟨-, e, rfl, ⟨rfl, -, rfl⟩ | ⟨rfl, -, rfl⟩⟩ := Relay.of_target_eq_segment hτ
          exacts [not_isDiag_segment j.isLt (hx.1 rfl), not_isDiag_segment j.isLt (hx.2 rfl).symm]
        · cases hτ
    obtain ⟨-, d₀, -⟩ := VertexMove.exists_fits (FL := FL) L j i ω
    obtain ⟨d, hd⟩ := VertexMove.exists_isPicked L (⟨j, i, ω, d₀⟩ : VertexMove FL)
    set t := (⟨j, i, ω, d⟩ : VertexMove FL).minUnits L
    have ht :
        moveCount lhat (initialCounts n) (outcomeOf R FL Pl o) (.vertex ⟨j, i, ω, d⟩) = t :=
      (moveCount_eq _).trans (ite_eq_left hd)
    have hrk : unitRank R FL Pl lhat n o u < FL.slotCount d q * t := by
      have h := rk_lt (idx := unitIndex R FL Pl) (key := unitTarget R FL Pl) (mem_aliveUnits.2 hu)
      rw [hτ, ← load_eq_card] at h
      exact h.trans_le (hd.1 q hq)
    have htpos : 0 < t := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hrk
    obtain ⟨e, -, he1, he2⟩ := exists_rk (idx := fun e => (Fintype.equivFin (FL.law d).Slot e : ℕ))
      (key := FL.slotPair d) (fun _ _ h => (Fintype.equivFin _).injective (Fin.ext h)) univ q
      (w := unitRank R FL Pl lhat n o u / t) ((Nat.div_lt_iff_lt_mul htpos).2 hrk)
    have he2' : FL.slotRank d e = unitRank R FL Pl lhat n o u / t := he2
    refine ⟨⟨.vertex ⟨j, i, ω, d⟩, e⟩, mem_givenUnits_vertex.2 ⟨hd, hu, by rw [hτ, he1], ?_, ?_⟩⟩
    · exact ht ▸ (Nat.mul_le_mul_right t he2.le).trans (Nat.div_mul_le_self _ _)
    · rw [ht, he2', add_mul, one_mul]
      exact Nat.lt_div_mul_add htpos

/-- **The current units in the end** ([AnthropicVPVNP2026], Theorem H.2(b), p. 46): an alive unit
that is current after all moves is done. -/
theorem unitTarget_eq_done_of_mem_cur {u : PlanUnit R FL Pl U0 U1}
    (hu : u ∈ (towerPlan R FL Pl lhat U0 U1).cur n o (Fintype.card (Move R ch FL)))
    (ha : IsAlive R FL Pl lhat n o u) : unitTarget R FL Pl u = .done := by
  by_contra hd
  obtain ⟨z, hz⟩ := exists_mem_givenUnits ha hd
  exact (Plan.mem_cur.1 hu).2 ((moveSlotEquiv R FL Pl).symm z)
    ((moveSlotEquiv R FL Pl).symm z).1.isLt
    (show u ∈ givenUnits R FL Pl lhat n o _ by rwa [Equiv.apply_symm_apply])

/-! ### The units between the nodes and their parents -/

variable (R FL Pl lhat n o) in
/-- The alive units between the node `P` and its parent: the alive units of the child channels of
`P`. -/
noncomputable def assignedUnits (P : T.Node) : Finset (PlanUnit R FL Pl U0 U1) :=
  (aliveUnits R FL Pl lhat n o).filter fun u =>
    ∃ ν k, u = .new ν k ∧ IsChild P (moveChannelEquiv R FL Pl ν)

/-- The new units between the node `P` and its parent: the alive units of the child channels of
`P`. -/
@[simp]
theorem new_mem_assignedUnits {P : T.Node} {ν : (moves R FL Pl).Channel} {k : Fin U1} :
    (.new ν k : PlanUnit R FL Pl U0 U1) ∈ assignedUnits R FL Pl lhat n o P ↔
      (k : ℕ) < alive lhat (initialCounts n) (outcomeOf R FL Pl o) (moveChannelEquiv R FL Pl ν) ∧
        IsChild P (moveChannelEquiv R FL Pl ν) := by
  simp only [assignedUnits, mem_filter, mem_aliveUnits, IsAlive, UnitId.new.injEq]
  exact ⟨fun ⟨h1, _, _, ⟨rfl, rfl⟩, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h1, ν, k, ⟨rfl, rfl⟩, h2⟩⟩

/-- The initial units are not between a node and its parent. -/
@[simp]
theorem init_notMem_assignedUnits {P : T.Node} {a c : Fin A} {k : Fin U0} :
    (.init a c k : PlanUnit R FL Pl U0 U1) ∉ assignedUnits R FL Pl lhat n o P := by
  simp [assignedUnits]

/-- **The units between a node and its parent** ([AnthropicVPVNP2026], Theorem H.2(b), p. 46):
the alive units of the child channels of a node are at most the units between the node and its
parent. -/
theorem card_assignedUnits_le (P : T.Node) :
    (assignedUnits R FL Pl lhat n o P).card ≤
      P.lift (T.parentUnits (edgeLoads (load lhat (initialCounts n) (outcomeOf R FL Pl o)))) 0 := by
  set e := moveChannelEquiv R FL Pl
  set al := alive lhat (initialCounts n) (outcomeOf R FL Pl o)
  calc (assignedUnits R FL Pl lhat n o P).card ≤ ((univ.filter fun ν => IsChild P (e ν)).biUnion
        fun ν => (univ.filter fun k : Fin U1 => (k : ℕ) < al (e ν)).image (.new ν)).card :=
        card_le_card fun u hu => by
          obtain ⟨-, ν, k, rfl, -⟩ := mem_filter.mp hu
          simpa using (new_mem_assignedUnits.mp hu).symm
    _ ≤ ∑ ν ∈ univ.filter fun ν => IsChild P (e ν), al (e ν) :=
        card_biUnion_le.trans (sum_le_sum fun ν _ => card_image_le.trans
          (by rw [Fin.card_filter_val_lt]; exact min_le_right _ _))
    _ = ∑ ν, if IsChild P ν then al ν else 0 :=
        (sum_filter _ _).trans (e.sum_comp fun ν => if IsChild P ν then al ν else 0)
    _ ≤ _ := sum_isChild_le P

variable (R FL Pl U0) in
/-- The dead units: the last unit of every channel, which is never moved again. -/
@[expose] noncomputable def deadUnits (o : (moves R FL Pl).Channel → Fin U1) :
    Finset (PlanUnit R FL Pl U0 U1) :=
  univ.image fun ν => .new ν (o ν)

/-! ### Possible outcomes -/

/-- An outcome of a move is good if it is the number of bits on its channels for an index for
every bit, over the number of bits of a unit. -/
private theorem goodOutcome_of_length {n : Fin A → Fin A → ℕ} {o : MoveChannel R ch FL → ℕ}
    {ub : ℕ} (hub : 0 < ub) {mv : Move R ch FL}
    (ι : Fin (moveCount lhat n o mv * ub) → mv.law.Index)
    (hι : ∀ ν, o ⟨mv, ν⟩ = (∑ k, (mv.law.labelLength + mv.law.length (ι k) ν)) / ub) :
    GoodOutcome lhat n o mv := by
  rcases mv with ⟨x, hx⟩ | l
  · intro ν
    rw [hι ν]
    simp [Move.law, relayLaw, Nat.mul_div_cancel _ hub]
  change l.OutcomeShort o (moveCount lhat n o (.vertex l)) ∧
    ∀ ν, moveCount lhat n o (.vertex l) ≤ o ⟨.vertex l, ν⟩
  revert ι
  generalize moveCount lhat n o (.vertex l) = t
  intro ι hι
  have hle (ν : (FL.law l.kind).Channel) : o ⟨.vertex l, ν⟩ * ub ≤
      ∑ k, ((FL.law l.kind).labelLength + (FL.law l.kind).length (ι k) ν) := by
    rw [hι ν]
    exact Nat.div_mul_le_self _ _
  refine ⟨Nat.le_of_mul_le_mul_right (c := ub ^ 2) ?_ (by positivity), fun ν => ?_⟩
  · calc (r * b * ∑ ν, o ⟨.vertex l, ν⟩ ^ 2) * ub ^ 2 =
          r * b * ∑ ν, (o ⟨.vertex l, ν⟩ * ub) ^ 2 := by
          simp only [mul_pow, sum_mul, mul_assoc]
      _ ≤ r * b * ∑ ν, (t * ub) *
          ∑ k, ((FL.law l.kind).labelLength + (FL.law l.kind).length (ι k) ν) ^ 2 := by
          refine Nat.mul_le_mul_left _ (sum_le_sum fun ν _ => ?_)
          have hcs := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin (t * ub))))
            (f := fun k => (FL.law l.kind).labelLength + (FL.law l.kind).length (ι k) ν)
          rw [card_univ, Fintype.card_fin] at hcs
          exact (Nat.pow_le_pow_left (hle ν) 2).trans hcs
      _ = (t * ub) *
          ∑ k, r * b * ∑ ν, ((FL.law l.kind).labelLength + (FL.law l.kind).length (ι k) ν) ^ 2 := by
          simp only [mul_sum]
          rw [sum_comm]
          exact sum_congr rfl fun k _ => sum_congr rfl fun ν _ => by ring
      _ ≤ (t * ub) * ∑ _k : Fin (t * ub), FL.lengthBound := by
          gcongr with k
          exact FL.sum_length_sq_le l.kind (ι k)
      _ = FL.lengthBound * t ^ 2 * ub ^ 2 := by
          simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
          ring
  · rw [hι ν, Nat.le_div_iff_mul_le hub]
    calc t * ub = ∑ _k : Fin (t * ub), 1 := by simp
      _ ≤ _ := sum_le_sum fun k _ => (FL.labelLength_pos l.kind).trans (Nat.le_add_right _ _)

/-- **Possible outcomes are good** ([AnthropicVPVNP2026], Section H.2, law moves, p. 45): an
outcome of a move of the tower plan that is possible for units of `ub > 0` bits is
good. -/
theorem towerPlan_good_of_possible {ub : ℕ} (hub : 0 < ub) {x : Fin (Fintype.card (Move R ch FL))}
    (hp : (towerPlan R FL Pl lhat U0 U1).Possible n o ub x) :
    (towerPlan R FL Pl lhat U0 U1).Good n o x := by
  obtain ⟨ι, hι⟩ := hp
  exact goodOutcome_of_length hub ι fun ν => (outcomeOf_moveOrder o x ν).trans (hι ν)

/-- For a good outcome, all units of a channel but the last are alive. -/
theorem alive_eq_of_goodOutcome {n : Fin A → Fin A → ℕ} {o : MoveChannel R ch FL → ℕ}
    {ν : MoveChannel R ch FL} (hg : GoodOutcome lhat n o ν.1) : alive lhat n o ν = o ν := by
  rcases ν with ⟨⟨x, hx⟩ | l, ν⟩
  · exact (ite_eq_left (hg ν)).trans (hg ν).symm
  · exact ite_eq_left hg.1

end Cslib.Circuits.Arithmetic.Separation.TowerPlan
