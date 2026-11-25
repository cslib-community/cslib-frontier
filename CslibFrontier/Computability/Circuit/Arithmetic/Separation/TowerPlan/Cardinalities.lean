/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.Plan
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Ring

/-!
# The sizes of the tower plan, and its placements

Theorem H.2(d) of [AnthropicVPVNP2026] (modules `Nc.Tow.Cards` and `Nc.Tow.PlaceE`) bounds the
numbers of nodes, moves and units that can occur in the tower plan by a power of `MN`. Here they
are bounded by powers of a number `V` that bounds the sizes of the tower, its routes and its laws
(`SizeBound`): the relays, the law moves and all moves, the channels, the slots and the roles of
the moves, the units of the play and the nodes of the tree. The units of the play are counted
exactly (`card_planUnit`). A placement of the nodes among the parties exists with the nodes that
are not at base parties as the extra parties (`exists_placement`).

## Main definitions

* `SizeBound`: the sizes of a tower, its routes and its laws are at most `V`.
* `numUnits`: the number of units of the play.

## Main results

* `card_relay_le`, `card_vertexMove_le`, `card_move_le`: the numbers of moves.
* `card_moveChannel_le`, `card_moveSlot_le`, `card_role_le`: the numbers of channels, slots and
  roles of the moves.
* `card_planUnit`, `card_planUnit_le`: the number of units of the play.
* `card_node_le`: the number of nodes of the tree.
* `Placement.card_node`, `exists_placement`: the parties of a placement are the nodes, and a
  placement exists.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Theorem H.2(d), p. 46, and its proof ("For (d)", p. 48); modules `Nc.Tow.Cards`,
  `Nc.Tow.PlaceE`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.TowerPlan

open Finset Cslib.CoveringTower Cut

variable {F : Type*} [CommSemiring F] {h b D J r m Uu A A' U0 U1 V : ℕ} {T : Tower h b D J r}
  {R : Routes T m Uu} {ch : Fin A ↪ T.X 0} {FL : VertexLaws F T}

variable (FL) in
/-- The sizes of a tower, its routes and its laws are at most `V`: the numbers of types, places,
edges of a type at a chamber, steps of a route, stages, base parties and chambers of the level `0`,
the number of kinds of laws and the numbers of slots of the laws; and `1 ≤ V`. -/
structure SizeBound (m A V : ℕ) : Prop where
  one_le : 1 ≤ V
  types_le : h ≤ V
  places_le : b ≤ V
  degree_le : r ≤ V
  length_le : m ≤ V
  stages_le : J ≤ V
  base_le : A ≤ V
  card_X_zero_le : Fintype.card (T.X 0) ≤ V
  card_kind_le : Fintype.card FL.Kind ≤ V
  card_slot_le : ∀ d, Fintype.card (FL.law d).Slot ≤ V

private theorem sum_move_le (g : Move R ch FL → ℕ) {a : ℕ} (ha : ∀ x hx, g (.relay x hx) ≤ a) :
    ∑ mv, g mv ≤ Fintype.card (Relay T m A) * a + ∑ l, g (.vertex l) := by
  rw [Move.sum_eq]
  refine add_le_add_left ((sum_le_card_nsmul _ _ a fun x _ => ?_).trans_eq (by simp)) _
  split_ifs with hx
  exacts [ha x hx, Nat.zero_le _]

variable (R ch FL) in
/-- The number of units of the play (`card_planUnit`): `U0` for every pair of base parties and
`U1` for every channel. It does not depend on the placement. -/
@[expose] def numUnits (U0 U1 : ℕ) : ℕ := A * A * U0 + Fintype.card (MoveChannel R ch FL) * U1

/-- The number of units of the play is `numUnits`. -/
theorem card_planUnit (Pl : Placement T ch A') :
    Fintype.card (PlanUnit R FL Pl U0 U1) = numUnits R ch FL U0 U1 := by
  rw [Fintype.card_eq_sum_ones, UnitId.sum_eq, numUnits,
    ← Fintype.card_congr (moveChannelEquiv R FL Pl)]
  simp [mul_assoc]

/-- The parties of a placement are the nodes of the tree. -/
theorem Placement.card_node (Pl : Placement T ch A') : Fintype.card T.Node = A + A' := by
  rw [Fintype.card_congr Pl.party, Fintype.card_fin]

variable (T ch) in
/-- **A placement exists**, with the nodes that are not at base parties as the extra parties. -/
theorem exists_placement : Nonempty (Placement T ch (Fintype.card T.Node - A)) := by
  classical
  let base : Fin A ↪ T.Node := ⟨fun a => .ofChamber (Nat.zero_le J) (ch a), fun a c hac =>
    ch.injective (Tower.Node.ofChamber_inj.1 hac)⟩
  have hc : Fintype.card ((Set.range base)ᶜ : Set T.Node) = Fintype.card T.Node - A := by
    rw [Fintype.card_compl_set, Set.card_range_of_injective base.injective, Fintype.card_fin]
  refine ⟨⟨(Equiv.Set.sumCompl (Set.range base)).symm.trans ((Equiv.sumCongr
    (Equiv.ofInjective base base.injective).symm (Fintype.equivFinOfCardEq hc)).trans
      finSumFinEquiv), fun a => ?_⟩⟩
  change finSumFinEquiv (Sum.map _ _ ((Equiv.Set.sumCompl (Set.range base)).symm (base a))) = _
  rw [Equiv.Set.sumCompl_symm_apply_of_mem (Set.mem_range_self a), Sum.map_inl,
    finSumFinEquiv_apply_left, Equiv.ofInjective_symm_apply]

variable (hD : 0 < D) (hV : SizeBound FL m A V)
include hD hV

private theorem card_Ed_le_pow {j : ℕ} (hj : j ≤ J) : Fintype.card (T.Ed j) ≤ V ^ 3 :=
  (Tower.card_Ed_le hD hj).trans <| by
    rw [pow_three, ← mul_assoc]
    exact Nat.mul_le_mul (Nat.mul_le_mul hV.types_le hV.degree_le) hV.card_X_zero_le

omit hD in
private theorem sum_stages_le {f : Fin J → ℕ} {B : ℕ} (hf : ∀ j, f j ≤ B) : ∑ j, f j ≤ V * B :=
  (sum_le_card_nsmul _ _ B fun j _ => hf j).trans <| by
    simpa using Nat.mul_le_mul_right B hV.stages_le

/-- The relays are at most `8 V ^ 5`. -/
theorem card_relay_le : Fintype.card (Relay T m A) ≤ 8 * V ^ 5 := by
  rw [Fintype.card_eq_sum_ones, Relay.sum_eq]
  simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  have h0 : A * (A * (Fintype.card (T.X 0) * (2 * m))) ≤ V * (V * (V * (2 * V))) :=
    Nat.mul_le_mul hV.base_le (Nat.mul_le_mul hV.base_le (Nat.mul_le_mul hV.card_X_zero_le
      (Nat.mul_le_mul_left 2 hV.length_le)))
  have h1 := sum_stages_le hV fun j : Fin J =>
    Nat.mul_le_mul hV.types_le (card_Ed_le_pow hD hV j.2.le)
  have h2 := sum_stages_le hV fun j : Fin J =>
    Nat.mul_le_mul_right 4 (card_Ed_le_pow hD hV j.2.le)
  have h3 := card_Ed_le_pow (T := T) hD hV le_rfl
  refine (add_le_add h0 (add_le_add h1 (add_le_add h2 h3))).trans ?_
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hV.one_le
  ring_nf
  omega

/-- The law moves are at most `V ^ 4`. -/
theorem card_vertexMove_le (hb : 0 < b) : Fintype.card (VertexMove FL) ≤ V ^ 4 := by
  rw [Fintype.card_eq_sum_ones, VertexMove.sum_eq]
  simp only [sum_const, card_univ, smul_eq_mul, mul_one]
  refine (sum_stages_le hV fun j : Fin J => (sum_le_card_nsmul _ _ (V * V) fun i _ =>
    Nat.mul_le_mul ((Tower.card_V_le hD hb j.2 i).trans hV.card_X_zero_le)
      hV.card_kind_le).trans (by simpa using Nat.mul_le_mul_right (V * V) hV.types_le)).trans_eq
    (by ring)

private theorem sum_vertexMove_le (hb : 0 < b) (g : VertexMove FL → ℕ)
    (hg : ∀ l, g l ≤ V) : ∑ l, g l ≤ V ^ 5 :=
  (sum_le_card_nsmul _ _ V fun l _ => hg l).trans <| by
    simpa [pow_succ] using Nat.mul_le_mul_right V (card_vertexMove_le hD hV hb)

private theorem card_relay_mul_add_le {a k : ℕ} (hk : 8 * a + 1 ≤ k) {s : ℕ} (hs : s ≤ V ^ 5) :
    Fintype.card (Relay T m A) * a + s ≤ k * V ^ 5 := by
  have := Nat.mul_le_mul_right a (card_relay_le (m := m) hD hV)
  nlinarith [Nat.mul_le_mul_right (V ^ 5) hk]

/-- The moves are at most `9 V ^ 5`. -/
theorem card_move_le (hb : 0 < b) : Fintype.card (Move R ch FL) ≤ 9 * V ^ 5 :=
  (Fintype.card_eq_sum_ones (α := Move R ch FL)).trans_le <|
    (sum_move_le _ fun _ _ => le_rfl).trans <| card_relay_mul_add_le hD hV (by norm_num)
      (sum_vertexMove_le hD hV hb _ fun _ => hV.one_le)

/-- The channels of the moves are at most `17 V ^ 6`. -/
theorem card_moveChannel_le : Fintype.card (MoveChannel R ch FL) ≤ 17 * V ^ 6 := by
  have h1 : ∑ l : VertexMove FL, Fintype.card (Move.vertex l : Move R ch FL).law.Channel ≤
      V ^ 6 := by
    rw [VertexMove.sum_eq]
    refine (sum_stages_le hV fun j => (sum_le_card_nsmul _ _ (V ^ 4) fun i _ => ?_).trans
      (by simpa using Nat.mul_le_mul_right _ hV.types_le)).trans_eq (by ring)
    calc _ = ∑ _ω : T.V (j + 1) i, ∑ _d : FL.Kind, Fintype.card T.Nr :=
          sum_congr rfl fun ω _ => sum_congr rfl fun d _ => Fintype.card_congr (FL.nearPair d)
      _ = Fintype.card FL.Kind * (Fintype.card (T.V (j + 1) i) * Fintype.card T.Nr) := by
          simp only [sum_const, card_univ, smul_eq_mul]
          ring
      _ ≤ V * V ^ 3 := Nat.mul_le_mul hV.card_kind_le ((Tower.card_V_mul_card_Nr_le j.2 i).trans
          (card_Ed_le_pow hD hV j.2))
      _ = V ^ 4 := by ring
  rw [Fintype.card_sigma]
  refine (sum_move_le _ (a := 2) fun _ _ => le_of_eq rfl).trans ?_
  have := Nat.mul_le_mul_right 2 (card_relay_le (m := m) hD hV)
  have := Nat.pow_le_pow_right hV.one_le (show 5 ≤ 6 by norm_num)
  omega

/-- The slots of the moves are at most `9 V ^ 5`. -/
theorem card_moveSlot_le (hb : 0 < b) : Fintype.card (MoveSlot R ch FL) ≤ 9 * V ^ 5 := by
  rw [Fintype.card_sigma]
  exact (sum_move_le _ (a := 1) fun _ _ => le_of_eq rfl).trans <| card_relay_mul_add_le hD hV
    (by norm_num) (sum_vertexMove_le hD hV hb _ fun l => hV.card_slot_le l.kind)

/-- The roles of the moves are at most `25 V ^ 5`. -/
theorem card_role_le (hb : 0 < b) (Pl : Placement T ch A') :
    Fintype.card (moves R FL Pl).Role ≤ 25 * V ^ 5 := by
  rw [Fintype.card_sigma]
  refine ((moveOrder R ch FL).sum_comp (fun mv => Fintype.card mv.law.Role)).trans_le ?_
  exact (sum_move_le _ (a := 3) fun _ _ => le_of_eq rfl).trans <| card_relay_mul_add_le hD hV
    (by norm_num) (sum_vertexMove_le hD hV hb _ fun l =>
      ((Fintype.card_congr (FL.place l.kind)).trans T.card_fl).trans_le hV.places_le)

/-- The units of the play are at most `18 V ^ 7` if `U0` and `U1` are at most `V`. -/
theorem card_planUnit_le (Pl : Placement T ch A') (hU0 : U0 ≤ V) (hU1 : U1 ≤ V) :
    Fintype.card (PlanUnit R FL Pl U0 U1) ≤ 18 * V ^ 7 := by
  rw [card_planUnit, numUnits]
  have h1 : A * A * U0 ≤ V * V * V := Nat.mul_le_mul (Nat.mul_le_mul hV.base_le hV.base_le) hU0
  have h2 := Nat.mul_le_mul (card_moveChannel_le (R := R) (ch := ch) hD hV) hU1
  have h3 : V * V * V ≤ V ^ 7 := by
    simpa [pow_three, mul_assoc] using Nat.pow_le_pow_right hV.one_le (show 3 ≤ 7 by norm_num)
  have h4 : 17 * V ^ 6 * V = 17 * V ^ 7 := by ring
  omega

/-- The nodes of the tree are at most `3 V ^ 2`. -/
theorem card_node_le : Fintype.card T.Node ≤ 3 * V ^ 2 := by
  rw [← Fintype.card_congr (proxy_equiv% T.Node)]
  simp only [Fintype.card_sum, Fintype.card_sigma, Fintype.card_unique]
  have : ∑ j : Fin (J + 1), Fintype.card (T.X j) ≤ (V + 1) * V :=
    (sum_le_card_nsmul _ _ V fun j _ => (Tower.card_X_le hD (Nat.le_of_lt_succ j.2)).trans
      hV.card_X_zero_le).trans <| by
        simpa using Nat.mul_le_mul_right V (Nat.succ_le_succ hV.stages_le)
  nlinarith [hV.one_le]

end Cslib.Circuits.Arithmetic.Separation.TowerPlan
