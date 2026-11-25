/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.Given
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.Plan
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.PlayMoves

/-!
# The tower plan: the units that a node ever holds

A party of the play of the tower plan of [AnthropicVPVNP2026] (proof of Theorem H.2; modules
`Nc.Tow.Ever4`, `Nc.Tow.Ever6`, `Nc.Tow.Ever7`) ever holds the initial units of its strings and
the units of the channels of the moves at it (`heldCount`); a role of a move reads the units of
its move at each of its slots, zeros included (`roleUnits`). For good outcomes, a relay puts on
its channels the units that it uses, and a law move at most `lengthBound` times as many on each
channel. With the units given at a node (`sum_unitsAt_relay_le`, `sum_unitsAt_vertex_le`), what
the party of a node ever holds and reads is at most the initial units of a base party and
`8 m lhat` more, one unit for every end of a channel at it (`channelEndCount`), and a constant
times the units between its chamber and the parent and between its children and the chamber.

## Main definitions

* `heldCount`: the number of units that a party ever holds.
* `channelEndCount`: the number of ends of channels at a party.
* `roleUnits`: the units that a role reads.

## Main results

* `heldCount_add_sum_roleUnits_le`: the units that a node ever holds and reads.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Theorem H.2(e), p. 46, and its proof ("For (e)", p. 48); modules `Nc.Tow.Ever4`,
  `Nc.Tow.Ever6`, `Nc.Tow.Ever7`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.TowerPlan

open Finset Cslib.CoveringTower Cut

variable {F : Type*} [CommSemiring F] {h b D J r m Uu A A' U0 U1 : ℕ} {T : Tower h b D J r}
  {R : Routes T m Uu} {ch : Fin A ↪ T.X 0} {FL : VertexLaws F T} {Pl : Placement T ch A'}
  {lhat : ℕ}

section Move

variable {n : Fin A → Fin A → ℕ} {o : MoveChannel R ch FL → ℕ}

/-- A short outcome of a law move puts at most `lengthBound` times the units of the move on each
channel. -/
private theorem le_lengthBound_mul (hr : 0 < r) (hb : 0 < b) {l : VertexMove FL} {t : ℕ}
    (hs : l.OutcomeShort o t) (c : (FL.law l.kind).Channel) :
    o ⟨.vertex l, c⟩ ≤ FL.lengthBound * t := by
  refine (Nat.pow_le_pow_iff_left two_ne_zero).1 (calc
    o ⟨.vertex l, c⟩ ^ 2 ≤ ∑ c', o ⟨.vertex l, c'⟩ ^ 2 :=
      single_le_sum (f := fun c' => o ⟨.vertex l, c'⟩ ^ 2) (fun _ _ => Nat.zero_le _)
        (mem_univ c)
    _ ≤ r * b * ∑ c', o ⟨.vertex l, c'⟩ ^ 2 := Nat.le_mul_of_pos_left _ (Nat.mul_pos hr hb)
    _ ≤ FL.lengthBound * t ^ 2 := hs
    _ ≤ (FL.lengthBound * t) ^ 2 := by
      rw [mul_pow]
      exact Nat.mul_le_mul_right _ (Nat.le_self_pow two_ne_zero _))

/-- The roles of a move at the node `P` read at most `1 + s` times the units given in the move at
`P`, if the law of the move has `s` slots. -/
private theorem sum_roles_le (P : T.Node) (mv : Move R ch FL) :
    ∑ q, (if mv.party q = P then (1 + Fintype.card (mv.law.SlotAt q)) * moveCount lhat n o mv
      else 0) ≤ (1 + Fintype.card mv.law.Slot) * unitsAt lhat n o P mv := by
  rw [unitsAt, mul_sum]
  refine sum_le_sum fun q _ => ?_
  split_ifs
  · exact Nat.mul_le_mul_right _ (Nat.add_le_add_left (Fintype.card_subtype_le _) 1)
  · exact Nat.zero_le _

/-- With good outcomes, the channels of a relay carry at the node `P` at most twice the units
given in the relay at `P`. -/
private theorem relay_ends_le (hg : ∀ mv, GoodOutcome lhat n o mv) {x : Relay T m A}
    (hx : x.Occurs R ch) (P : T.Node) :
    (∑ c : Bool, ∑ d : Bool, if x.party R ch (relayChannelEnd c d) = P then
      o ⟨.relay x hx, c⟩ else 0) ≤
      2 * ∑ q : RelayRole, if x.party R ch q = P then moveCount lhat n o (.relay x hx)
        else 0 := by
  have hc (c : Bool) : o ⟨.relay x hx, c⟩ = moveCount lhat n o (.relay x hx) :=
    hg (.relay x hx) c
  simp only [Fintype.sum_bool, relayChannelEnd, Bool.cond_true, Bool.cond_false,
    RelayRole.sum_univ, hc]
  grind

/-- With good outcomes, the channels of a law move carry at the node `P` at most
`2 |Nr| lengthBound` times the units given in the move at `P`. -/
private theorem vertex_ends_le (hr : 0 < r) (hb : 0 < b) (hg : ∀ mv, GoodOutcome lhat n o mv)
    (P : T.Node) (l : VertexMove FL) :
    (∑ c, ∑ d, if (Move.vertex l : Move R ch FL).party ((FL.law l.kind).channelEnd c d) = P then
      o ⟨.vertex l, c⟩ else 0) ≤
      2 * Fintype.card T.Nr * FL.lengthBound * unitsAt lhat n o P (.vertex l) := by
  calc _ ≤ ∑ _c : (FL.law l.kind).Channel, ∑ _d : Bool,
        FL.lengthBound * unitsAt lhat n o P (.vertex l) := by
        gcongr with c _ d _
        split_ifs with hq
        · refine (le_lengthBound_mul hr hb (hg (.vertex l)).1 c).trans (Nat.mul_le_mul_left _ ?_)
          exact (ite_eq_left hq).symm.trans_le (single_le_sum (f := fun q =>
            if (Move.vertex l : Move R ch FL).party q = P then moveCount lhat n o (.vertex l)
            else 0) (fun _ _ => Nat.zero_le _) (mem_univ _))
        · exact Nat.zero_le _
    _ = _ := by
        simp only [sum_const, card_univ, Fintype.card_bool, smul_eq_mul,
          Fintype.card_congr (FL.nearPair l.kind)]
        ring

end Move

variable (R FL Pl lhat) (n : Fin A → Fin A → Fin (U0 + 1))
  (o : (moves R FL Pl).Channel → Fin U1)

/-- The number of units that the party `p` ever holds: the units seen after all moves that it
holds. -/
@[expose] noncomputable def heldCount (p : Fin (A + A')) : ℕ :=
  ((Plan.seenAt n o (Fintype.card (Move R ch FL))).filter
    (Play.Holds (UnitId.holder (moves R FL Pl).channelParty) p)).card

/-- The number of ends of channels of the moves at the party `p`. -/
@[expose] noncomputable def channelEndCount (p : Fin (A + A')) : ℕ :=
  ∑ ν : (moves R FL Pl).Channel, ∑ d : Bool,
    if (moves R FL Pl).channelParty ν d = p then 1 else 0

/-- The units that the role `ρ` reads: the units of its move at each slot of the role, zeros
included, and once more the number of units of its move. -/
@[expose] noncomputable def roleUnits (ρ : (moves R FL Pl).Role) : ℕ :=
  (1 + Fintype.card (((moves R FL Pl).law ρ.1).SlotAt ρ.2)) *
    (towerPlan R FL Pl lhat U0 U1).count n o ρ.1

variable {R FL Pl lhat n o}

/-- The units that the party of a node holds: the initial units of a base party, and the units
of the channels at it. -/
private theorem heldCount_le {ℓf : ℕ} (P : T.Node)
    (hini : ∀ a, Tower.Node.ofChamber (Nat.zero_le J) (ch a) = P →
      ∑ c, ((n a c : ℕ) + n c a) ≤ ℓf) :
    heldCount R FL Pl n o (Pl.party P) ≤
      (if ∃ a, Tower.Node.ofChamber (Nat.zero_le J) (ch a) = P then ℓf else 0) +
        channelEndCount R FL Pl (Pl.party P) + ∑ ν, ∑ d,
          if (moves R FL Pl).channelParty ν d = Pl.party P then (o ν : ℕ) else 0 := by
  have hp (a : Fin A) :
      Pl.party P = Fin.castAdd A' a ↔ Tower.Node.ofChamber (Nat.zero_le J) (ch a) = P := by
    rw [← Pl.party_base, Pl.party.injective.eq_iff, eq_comm]
  rw [heldCount, Plan.card_filter_holds_seenAt, filter_true_of_mem fun ν _ => ν.1.isLt, add_assoc]
  refine add_le_add ?_ (le_of_eq ?_)
  · simp only [hp]
    split_ifs with hB
    · obtain ⟨a₀, rfl⟩ := hB
      simp only [Tower.Node.ofChamber_inj, ch.injective.eq_iff]
      refine le_trans (sum_le_sum fun a _ => sum_le_sum fun c _ =>
        (show _ ≤ (if a = a₀ then (n a c : ℕ) else 0) +
          if c = a₀ then (n a c : ℕ) else 0 by
          split_ifs <;> omega)) ?_
      simpa [sum_add_distrib, sum_ite_eq'] using hini a₀ rfl
    · exact (sum_eq_zero fun a _ => sum_eq_zero fun c _ => ite_eq_right fun h =>
        hB (h.elim (fun h => ⟨a, h⟩) fun h => ⟨c, h⟩)).le
  · rw [channelEndCount, ← sum_add_distrib]
    exact sum_congr rfl fun ν _ => (sum_congr rfl fun d _ => by split_ifs <;> omega).trans
      sum_add_distrib

/-- **The units that a node ever holds** ([AnthropicVPVNP2026], Theorem H.2(e), p. 46): for
good outcomes, if every place is an end of a near pair, every law has at most `Sm` slots and a
base party has at most `ℓf` initial units, the party of a node ever holds and its roles read at
most `ℓf + 8 m lhat` units at a base party, one unit for every end of a channel at it, and
`4 + (2 |Nr| lengthBound + 1 + Sm) |Kind|` times `8` times the units between its chamber and the
parent and `3` times those between its children and the chamber (at the root: the loads of the
last level). -/
theorem heldCount_add_sum_roleUnits_le (hr : 0 < r) (hb : 0 < b) (hh : 0 < h)
    (hg : ∀ x, (towerPlan R FL Pl lhat U0 U1).Good n o x)
    (hnr : ∀ f : T.Fl, ∃ ν, T.cN ν = f ∨ T.dN ν = f) {Sm : ℕ}
    (hSm : ∀ d, Fintype.card (FL.law d).Slot ≤ Sm) {ℓf : ℕ} (P : T.Node)
    (hini : ∀ a, Tower.Node.ofChamber (Nat.zero_le J) (ch a) = P →
      ∑ c, ((n a c : ℕ) + n c a) ≤ ℓf) :
    heldCount R FL Pl n o (Pl.party P) + ∑ ρ, (if (moves R FL Pl).roleParty ρ = Pl.party P then
        roleUnits R FL Pl lhat n o ρ else 0) ≤
      (if ∃ a, Tower.Node.ofChamber (Nat.zero_le J) (ch a) = P then ℓf + 8 * m * lhat else 0) +
        channelEndCount R FL Pl (Pl.party P) +
        (4 + (2 * Fintype.card T.Nr * FL.lengthBound + 1 + Sm) * Fintype.card FL.Kind) *
          P.lift (fun j c =>
            8 * T.parentUnits (edgeLoads (load lhat (initialCounts n) (outcomeOf R FL Pl o))) j c +
            3 * T.childUnits hh (edgeLoads (load lhat (initialCounts n) (outcomeOf R FL Pl o))) j c)
            (∑ e, edgeLoads (load lhat (initialCounts n) (outcomeOf R FL Pl o)) J e) := by
  have hg' (mv : Move R ch FL) :
      GoodOutcome lhat (initialCounts n) (outcomeOf R FL Pl o) mv := by
    exact (moveOrder R ch FL).apply_symm_apply mv ▸ hg _
  -- the channels and the roles, by the moves
  have hch : (∑ ν, ∑ d, if (moves R FL Pl).channelParty ν d = Pl.party P then (o ν : ℕ)
      else 0) =
      ∑ mv : Move R ch FL, ∑ c, ∑ d, if mv.party (mv.law.channelEnd c d) = P then
        outcomeOf R FL Pl o ⟨mv, c⟩ else 0 := by
    refine (sum_congr rfl fun ν _ => sum_congr rfl fun d _ =>
      if_congr Pl.party.injective.eq_iff (by simp [outcomeOf]) rfl).trans
      (((moveChannelEquiv R FL Pl).sum_comp fun ν : MoveChannel R ch FL => ∑ d,
        if ν.1.party (ν.1.law.channelEnd ν.2 d) = P then outcomeOf R FL Pl o ν else 0).trans
        (Fintype.sum_sigma _))
  have hro : (∑ ρ, if (moves R FL Pl).roleParty ρ = Pl.party P then
      roleUnits R FL Pl lhat n o ρ else 0) = ∑ mv : Move R ch FL, ∑ q, if mv.party q = P then
        (1 + Fintype.card (mv.law.SlotAt q)) *
          moveCount lhat (initialCounts n) (outcomeOf R FL Pl o) mv else 0 := by
    refine (sum_congr rfl fun ρ _ => if_congr Pl.party.injective.eq_iff rfl rfl).trans
      (((Equiv.sigmaCongrLeft (β := fun mv : Move R ch FL => mv.law.Role)
        (moveOrder R ch FL)).sum_comp fun y => if y.1.party y.2 = P then
          (1 + Fintype.card (y.1.law.SlotAt y.2)) *
            moveCount lhat (initialCounts n) (outcomeOf R FL Pl o) y.1 else 0).trans
        (Fintype.sum_sigma _))
  -- every move, by the units given in it at the node
  have hmv : ∑ mv : Move R ch FL, ((∑ c, ∑ d, if mv.party (mv.law.channelEnd c d) = P then
      outcomeOf R FL Pl o ⟨mv, c⟩ else 0) + ∑ q, if mv.party q = P then
        (1 + Fintype.card (mv.law.SlotAt q)) *
          moveCount lhat (initialCounts n) (outcomeOf R FL Pl o) mv else 0) ≤
      4 * (∑ x, if hx : x.Occurs R ch then
        unitsAt lhat (initialCounts n) (outcomeOf R FL Pl o) P (.relay x hx) else 0) +
      (2 * Fintype.card T.Nr * FL.lengthBound + 1 + Sm) *
        ∑ l, unitsAt lhat (initialCounts n) (outcomeOf R FL Pl o) P (.vertex l) := by
    rw [Move.sum_eq, mul_sum, mul_sum]
    refine add_le_add (sum_le_sum fun x _ => ?_) (sum_le_sum fun l _ => ?_)
    · split_ifs with hx
      · have h1 := relay_ends_le hg' hx P
        have h2 := sum_roles_le (lhat := lhat) (n := initialCounts n) (o := outcomeOf R FL Pl o)
          P (.relay x hx)
        have h3 : Fintype.card (Move.relay x hx : Move R ch FL).law.Slot = 1 := Fintype.card_unit
        rw [h3] at h2
        change _ ≤ 2 * unitsAt lhat (initialCounts n) (outcomeOf R FL Pl o) P (.relay x hx) at h1
        exact (add_le_add h1 h2).trans_eq (by ring)
      · exact le_rfl
    · exact (add_le_add (vertex_ends_le hr hb hg' P l)
        ((sum_roles_le P (.vertex l)).trans
          (Nat.mul_le_mul_right _ (Nat.add_le_add_left (hSm l.kind) 1)))).trans_eq (by ring)
  have h1 := heldCount_le (R := R) (FL := FL) (Pl := Pl) (n := n) (o := o) P hini
  have h2 := sum_unitsAt_relay_le hh hg' P
  have h3 := sum_unitsAt_vertex_le hg' hnr P
  set L := edgeLoads (load lhat (initialCounts n) (outcomeOf R FL Pl o))
  set G := P.lift (fun j c => 8 * T.parentUnits L j c + 3 * T.childUnits hh L j c) (∑ e, L J e)
  set K := 2 * Fintype.card T.Nr * FL.lengthBound + 1 + Sm
  have h4 : K * ∑ l, unitsAt lhat (initialCounts n) (outcomeOf R FL Pl o) P (.vertex l) ≤
      K * Fintype.card FL.Kind * G := calc
    _ ≤ K * (Fintype.card FL.Kind * P.lift (T.parentUnits L) 0) := Nat.mul_le_mul_left _ h3
    _ ≤ K * (Fintype.card FL.Kind * G) := by
      gcongr
      cases P <;> simp [Tower.Node.lift, G]
      omega
    _ = _ := by ring
  rw [hch] at h1
  rw [hro, show (4 + K * Fintype.card FL.Kind) * G = 4 * G + K * Fintype.card FL.Kind * G by ring]
  rw [sum_add_distrib] at hmv
  have h5 : 8 * m * lhat = 4 * (2 * m * lhat) := by ring
  split_ifs at h1 h2 ⊢ <;> omega

end Cslib.Circuits.Arithmetic.Separation.TowerPlan
