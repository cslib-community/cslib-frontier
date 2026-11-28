/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.Moves
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.Laws
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.Relays
import Mathlib.Data.Fin.Tuple.Sort

/-!
# The tower plan: its moves

The moves of the tower plan of [AnthropicVPVNP2026] (proof of Theorem H.2; module `Nc.Tow.Net`)
are the relays of the plan (`Move.relay`) and, for every vertex of the next level at every stage
and every kind of law, a law move at the chambers of that vertex (`Move.vertex`). They are put in
an order in which their times do not decrease (`moveOrder`), and with a placement of the nodes
of the tree among the parties (`Placement`) they are the moves of a play (`moves`).

## Main definitions

* `VertexMove`, `VertexMove.withKind`, `Move`: the law moves at the vertices, and all moves.
* `Move.law`, `Move.party`, `Move.time`, `Move.target`, `Move.isVertex`: the law of a move, the
  nodes at its roles, its time, the targets of its channels, and whether it is a law move.
* `Placement`: the party of every node of the tree.
* `moveOrder`, `moves`: the order of the moves, and the moves as `Cut.Moves`.
* `MoveChannel`, `MoveSlot`, `moveChannelEquiv`, `moveSlotEquiv`: the channels and the slots of
  the moves, by their moves.

## Main results

* `VertexMove.sum_eq`, `Move.sum_eq`: sums over the law moves and over all moves.
* `Move.party_injective`: the nodes at the roles of a move are different.
* `Move.time_lt_time_target`: the units of the channels of a move are given later.
* `lt_of_time_moveOrder_lt`: a move with a smaller time comes earlier in the order.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Theorem H.2 (proof: "One stage"); module `Nc.Tow.Net`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.TowerPlan

open Finset Cslib.CoveringTower Cut

variable {F : Type*} [CommSemiring F] {h b D J r m Uu A A' : ℕ} {T : Tower h b D J r}

/-- A law move of the plan: a law of the kind `kind` is applied at the chambers of the vertex
`vertex` of the level `stage + 1`. -/
structure VertexMove (FL : VertexLaws F T) where
  /-- The stage of the move: the vertex is in the next level. -/
  stage : Fin J
  /-- The type of the vertex. -/
  type : Fin h
  /-- The vertex. -/
  vertex : T.V (stage + 1) type
  /-- The kind of the law. -/
  kind : FL.Kind

instance (FL : VertexLaws F T) : DecidableEq (VertexMove FL) :=
  (proxy_equiv% (VertexMove FL)).symm.decidableEq

instance (FL : VertexLaws F T) : Fintype (VertexMove FL) :=
  Fintype.ofEquiv _ (proxy_equiv% (VertexMove FL))

/-- A sum over the law moves, by their stages, types, vertices and kinds. -/
theorem VertexMove.sum_eq {FL : VertexLaws F T} {M : Type*} [AddCommMonoid M]
    (g : VertexMove FL → M) : ∑ l, g l = ∑ j, ∑ i, ∑ ω, ∑ d, g ⟨j, i, ω, d⟩ := by
  rw [← (proxy_equiv% (VertexMove FL)).sum_comp]
  simp only [Fintype.sum_sigma]
  rfl

/-- The same vertex with another kind of law. -/
@[expose] def VertexMove.withKind {FL : VertexLaws F T} (l : VertexMove FL) (d : FL.Kind) :
    VertexMove FL :=
  { l with kind := d }

/-- The moves of the tower plan. -/
inductive Move (R : Routes T m Uu) (ch : Fin A ↪ T.X 0) (FL : VertexLaws F T) where
  /-- A relay of the plan. -/
  | relay (x : Relay T m A) (hx : x.Occurs R ch)
  /-- A law move at a vertex. -/
  | vertex (l : VertexMove FL)

instance (R : Routes T m Uu) (ch : Fin A ↪ T.X 0) (FL : VertexLaws F T) :
    DecidableEq (Move R ch FL) :=
  (proxy_equiv% (Move R ch FL)).symm.decidableEq

instance (R : Routes T m Uu) (ch : Fin A ↪ T.X 0) (FL : VertexLaws F T) :
    Fintype (Move R ch FL) :=
  Fintype.ofEquiv _ (proxy_equiv% (Move R ch FL))

namespace Move

variable {R : Routes T m Uu} {ch : Fin A ↪ T.X 0} {FL : VertexLaws F T}

/-- A sum over the moves: the relays of the plan and the law moves. -/
theorem sum_eq {M : Type*} [AddCommMonoid M] (g : Move R ch FL → M) :
    ∑ mv, g mv = (∑ x, if hx : x.Occurs R ch then g (.relay x hx) else 0) + ∑ l, g (.vertex l) := by
  rw [← (proxy_equiv% (Move R ch FL)).sum_comp]
  simp only [Fintype.sum_sum_type, Fintype.sum_sigma]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs with hx
  · exact Fintype.sum_eq_single ⟨hx⟩ fun y hy => absurd rfl hy
  · have : IsEmpty (PLift (x.Occurs R ch)) := ⟨fun y => hx y.down⟩
    exact Fintype.sum_empty _

/-- The move is a law move at a vertex. -/
@[expose] def isVertex : Move R ch FL → Bool
  | .relay _ _ => false
  | .vertex _ => true

/-- The law of a move. -/
@[expose] def law : Move R ch FL → Law F
  | .relay _ _ => relayLaw F
  | .vertex l => FL.law l.kind

/-- The nodes at the roles of a move. -/
@[expose] noncomputable def party : (mv : Move R ch FL) → mv.law.Role → T.Node
  | .relay x _ => x.party R ch
  | .vertex l => fun p => .ofChamber l.stage.2
      ((T.chamberEquiv l.stage.2 l.type).symm (l.vertex, FL.place l.kind p))

/-- The nodes at the roles of a move are different. -/
theorem party_injective (mv : Move R ch FL) : Function.Injective mv.party := by
  rcases mv with ⟨x, hx⟩ | l
  · exact Relay.party_injective hx
  · intro p q hpq
    have h1 := Tower.Node.ofChamber_inj (hj := l.stage.2) (hj' := l.stage.2) |>.1 hpq
    exact (FL.place l.kind).injective (by simpa using congrArg (T.co l.type) h1)

/-- The time of a move: the law moves of a stage come after its relays. -/
@[expose] def time : Move R ch FL → ℕ
  | .relay x _ => x.time m
  | .vertex l => 2 * m + 6 * l.stage + 4

/-- The targets of the channels of a move: the channels of a law move are the edges of the next
level at its vertex. -/
@[expose] noncomputable def target : (mv : Move R ch FL) → mv.law.Channel → Target T m A
  | .relay x _ => x.target R ch
  | .vertex l => fun ν => .edge l.stage.succ
      ((T.nr l.stage.2 l.type).symm (l.vertex, FL.nearPair l.kind ν)).1

theorem time_lt_endTime (mv : Move R ch FL) : mv.time < endTime J m := by
  rcases mv with ⟨x, hx⟩ | l
  · exact x.time_lt_endTime
  · have := l.stage.2
    simp only [time, endTime]
    omega

/-- The units of the channels of a move are given later. -/
theorem time_lt_time_target (mv : Move R ch FL) (ν : mv.law.Channel) :
    mv.time < (mv.target ν).time := by
  rcases mv with ⟨x, hx⟩ | l
  · exact x.time_lt_time_target ν
  · simp only [time, target, Target.time, Fin.val_succ]
    omega

end Move

/-- Where the nodes of the tree are among the parties: the chambers of the base parties are at
the base parties. -/
structure Placement (T : Tower h b D J r) (ch : Fin A ↪ T.X 0) (A' : ℕ) where
  /-- The party of a node. -/
  party : T.Node ≃ Fin (A + A')
  party_base : ∀ a, party (.ofChamber (Nat.zero_le J) (ch a)) = Fin.castAdd A' a

section Moves

variable (R : Routes T m Uu) (ch : Fin A ↪ T.X 0) (FL : VertexLaws F T)

/-- The order of the moves: their times do not decrease. -/
noncomputable def moveOrder : Fin (Fintype.card (Move R ch FL)) ≃ Move R ch FL :=
  (Tuple.sort (Move.time ∘ (Fintype.equivFin (Move R ch FL)).symm)).trans
    (Fintype.equivFin (Move R ch FL)).symm

variable {R ch FL} in
/-- A move with a smaller time comes earlier in the order. -/
theorem lt_of_time_moveOrder_lt {x y : Fin (Fintype.card (Move R ch FL))}
    (hxy : (moveOrder R ch FL x).time < (moveOrder R ch FL y).time) : x < y :=
  (Tuple.monotone_sort (Move.time ∘ (Fintype.equivFin (Move R ch FL)).symm)).reflect_lt hxy

/-- The channels of the moves, by their moves. -/
abbrev MoveChannel : Type := Σ mv : Move R ch FL, mv.law.Channel

/-- The slots of the moves, by their moves. -/
abbrev MoveSlot : Type := Σ mv : Move R ch FL, mv.law.Slot

variable {ch} (Pl : Placement T ch A')

/-- The moves of the tower plan, in their order, with the parties of the nodes at their
roles. -/
@[expose] noncomputable def moves : Moves F (A + A') (Fintype.card (Move R ch FL)) where
  law x := (moveOrder R ch FL x).law
  party x p := Pl.party ((moveOrder R ch FL x).party p)
  party_injective x := Pl.party.injective.comp (moveOrder R ch FL x).party_injective

/-- The channels of the moves of the play are the channels of the moves of the plan. -/
@[expose] noncomputable def moveChannelEquiv : (moves R FL Pl).Channel ≃ MoveChannel R ch FL :=
  Equiv.sigmaCongrLeft (β := fun mv : Move R ch FL => mv.law.Channel) (moveOrder R ch FL)

/-- The slots of the moves of the play are the slots of the moves of the plan. -/
@[expose] noncomputable def moveSlotEquiv : (moves R FL Pl).Slot ≃ MoveSlot R ch FL :=
  Equiv.sigmaCongrLeft (β := fun mv : Move R ch FL => mv.law.Slot) (moveOrder R ch FL)

variable {R FL Pl}

@[simp]
theorem fst_moveChannelEquiv (ν : (moves R FL Pl).Channel) :
    (moveChannelEquiv R FL Pl ν).1 = moveOrder R ch FL ν.1 := rfl

@[simp]
theorem fst_moveSlotEquiv (z : (moves R FL Pl).Slot) :
    (moveSlotEquiv R FL Pl z).1 = moveOrder R ch FL z.1 := rfl

/-- The parties at the ends of a channel are the parties of the nodes of its move. -/
theorem channelParty_moves (ν : (moves R FL Pl).Channel) (d : Bool) :
    (moves R FL Pl).channelParty ν d = Pl.party ((moveChannelEquiv R FL Pl ν).1.party
      ((moveChannelEquiv R FL Pl ν).1.law.channelEnd (moveChannelEquiv R FL Pl ν).2 d)) := rfl

/-- The parties at the ends of a slot are the parties of the nodes of its move. -/
theorem slotParty_moves (z : (moves R FL Pl).Slot) (d : Bool) :
    (moves R FL Pl).slotParty z d = Pl.party ((moveSlotEquiv R FL Pl z).1.party
      ((moveSlotEquiv R FL Pl z).1.law.slotEnd (moveSlotEquiv R FL Pl z).2 d)) := rfl

end Moves

end Cslib.Circuits.Arithmetic.Separation.TowerPlan
