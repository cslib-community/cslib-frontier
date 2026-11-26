/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.Groups
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.Capacity
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.EndUnits
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.PlayMoves
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.EverHeld

/-!
# The tree of the tower plan

The networks of Theorem H.2 of [AnthropicVPVNP2026] (pp. 45–46) are trees: the nodes of the tree
of a covering tower (`Cslib.CoveringTower.Tower.Node`), placed among the parties of the tower plan
(`TowerPlan.Placement`). For the numbers `n` of initial units and the outcomes `o`, the parent of a
party is the party of the parent of its node for the loads of the plan (`treeParent`), and the
units between a party and its parent are the units between its chamber and the parent chamber
(`treeUnits`, `0` at the root).

For good outcomes, every unit that is current after all moves and is not dead joins a node and
its parent, or stays at one party (`exists_parent`), and the units between a party and its parent
are at most `treeUnits` (`card_between_le`). The units of a party and its children add up to at
most a constant times `edgeUnitBound` (`treeUnits_add_sum_le`), and all of them to at most
`treeUnitBound` (`sum_treeUnits_le`). The numbers of units of the law moves at a party are at
most the units that it ever holds (`sum_count_le_card_seenAt`), and these, with the units that its
roles read, are at most a constant times the units of the party and its children, the dead units
at it and the initial units of a base party (`card_held_add_le`).

## Main definitions

* `treeParent`, `treeUnits`: the parent of a party, and the units between a party and its parent.

## Main results

* `card_children_le`, `card_children_root_le`: the children of a party.
* `exists_parent`, `card_between_le`: the units in the end.
* `treeUnits_add_sum_le`, `sum_treeUnits_le`: the units between the parties and their parents.
* `sum_count_le_card_seenAt`: the layers of the law moves at a party.
* `card_held_add_le`: the units that a party ever holds and reads.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Theorem H.2(a), (b), (c), (e), pp. 45–46, and its proof ("Bounds", p. 47; "For (e)", p. 48);
  module `Paper.Tree`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Trees

open Finset Cslib.CoveringTower Cut TowerPlan

variable {F : Type*} [CommSemiring F] {h b D J r m Uu A A' U0 U1 : ℕ} {T : Tower h b D J r}
  {R : Routes T m Uu} {ch : Fin A ↪ T.X 0} {FL : VertexLaws F T} {Pl : Placement T ch A'}
  {lhat : ℕ}

section Defs

variable (R FL Pl) (hh : 0 < h) (lhat : ℕ) (n : Fin A → Fin A → Fin (U0 + 1))
  (o : (moves R FL Pl).Channel → Fin U1)

/-- The parent of a party in the tree of the tower plan: the party of the parent of its node, for
the loads of the plan. -/
@[expose] noncomputable def treeParent (p : Fin (A + A')) : Fin (A + A') :=
  Pl.party ((Pl.party.symm p).parent hh
    (edgeLoads (load lhat (initialCounts n) (outcomeOf R FL Pl o))))

/-- The units between a party and its parent in the tree of the tower plan: the units between
its chamber and the parent chamber, and `0` at the root. -/
@[expose] noncomputable def treeUnits (p : Fin (A + A')) : ℕ :=
  (Pl.party.symm p).lift
    (T.parentUnits (edgeLoads (load lhat (initialCounts n) (outcomeOf R FL Pl o)))) 0

end Defs

variable {n : Fin A → Fin A → Fin (U0 + 1)} {o : (moves R FL Pl).Channel → Fin U1}

/-- Sums over the children of a party are sums over the children of its node. -/
private theorem sum_children_eq (hh : 0 < h) {M : Type*} [AddCommMonoid M]
    (f : Fin (A + A') → M) (p : Fin (A + A')) :
    ∑ q ∈ univ.filter (fun q => q ≠ Pl.party .root ∧ treeParent R FL Pl hh lhat n o q = p), f q =
      ∑ Q ∈ univ.filter (fun Q : T.Node => Q ≠ .root ∧ Q.parent hh
        (edgeLoads (load lhat (initialCounts n) (outcomeOf R FL Pl o))) = Pl.party.symm p),
        f (Pl.party Q) :=
  sum_equiv Pl.party.symm (fun q => by
    simp [treeParent, ← Equiv.eq_symm_apply]) fun q _ => by simp

/-- **The children of a party** ([AnthropicVPVNP2026], Theorem H.2(a), p. 45): a party other than
the root has at most `b` children. -/
theorem card_children_le (hh : 0 < h) {p : Fin (A + A')} (hp : p ≠ Pl.party .root) :
    (univ.filter fun q => q ≠ Pl.party .root ∧ treeParent R FL Pl hh lhat n o q = p).card ≤ b := by
  rw [card_eq_sum_ones, sum_children_eq hh, ← card_eq_sum_ones]
  exact Tower.Node.card_children_le hh _ fun h0 => hp (by rw [← h0, Equiv.apply_symm_apply])

/-- The root has at most as many children as the last level has chambers. -/
theorem card_children_root_le (hh : 0 < h) :
    (univ.filter fun q => q ≠ Pl.party .root ∧
      treeParent R FL Pl hh lhat n o q = Pl.party .root).card ≤ Fintype.card (T.X J) := by
  rw [card_eq_sum_ones, sum_children_eq hh, ← card_eq_sum_ones, Equiv.symm_apply_apply]
  exact Tower.Node.card_children_root_le hh _

/-- The base parties are the parties of the chambers of the base. -/
private theorem exists_base_iff (P : T.Node) :
    (∃ a, Tower.Node.ofChamber (Nat.zero_le J) (ch a) = P) ↔ (Pl.party P : ℕ) < A := by
  refine ⟨fun ⟨a, ha⟩ => ha ▸ (Pl.party_base a).symm ▸ a.2, fun hP => ⟨⟨_, hP⟩, ?_⟩⟩
  refine Pl.party.injective ((Pl.party_base _).trans (Fin.ext rfl))

/-! ### The units in the end -/

section End

variable (hh : 0 < h) (hn : InitialBound lhat (initialCounts n))
  (hg : ∀ x, (towerPlan R FL Pl lhat U0 U1).Good n o x)
include hn hg

omit hn in
private theorem goodOutcome_of_good (mv : Move R ch FL) :
    GoodOutcome lhat (initialCounts n) (outcomeOf R FL Pl o) mv :=
  (moveOrder R ch FL).apply_symm_apply mv ▸ hg _

/-- A unit that is current after all moves, is not dead and joins two parties is a unit between a
node other than the root and its parent. -/
private theorem exists_node_of_mem_cur {u : PlanUnit R FL Pl U0 U1}
    (hu : u ∈ (towerPlan R FL Pl lhat U0 U1).cur n o (Fintype.card (Move R ch FL)))
    (hd : u ∉ deadUnits U0 R FL Pl o)
    (hne : UnitId.holder (moves R FL Pl).channelParty u false ≠
      UnitId.holder (moves R FL Pl).channelParty u true) :
    ∃ P : T.Node, P ≠ .root ∧ u ∈ assignedUnits R FL Pl lhat n o P ∧
      s(UnitId.holder (moves R FL Pl).channelParty u false,
        UnitId.holder (moves R FL Pl).channelParty u true) =
        s(Pl.party P, Pl.party (P.parent hh
          (edgeLoads (load lhat (initialCounts n) (outcomeOf R FL Pl o))))) := by
  have hseen := (Plan.mem_cur.1 hu).1
  obtain ⟨a, c, k⟩ | ⟨ν, k⟩ := u
  · have hdone := unitTarget_eq_done_of_mem_cur hu ⟨hn, Plan.init_mem_seenAt.1 hseen⟩
    refine absurd ?_ hne
    simp only [unitTarget, initialTarget] at hdone
    split_ifs at hdone with hac hs
    · exact hac ▸ rfl
    · exact absurd hdone (stepTarget_ne_done (R.pl_pos (fun e => hac (ch.injective e)) _))
  obtain ⟨-, hk⟩ := Plan.new_mem_seenAt.1 hseen
  have hlt : (k : ℕ) < o ν := lt_of_le_of_ne hk fun e =>
    hd (mem_image.2 ⟨ν, mem_univ _, by rw [Fin.ext e]⟩)
  have hgo := goodOutcome_of_good hg (moveChannelEquiv R FL Pl ν).1
  have halive : alive lhat (initialCounts n) (outcomeOf R FL Pl o)
      (moveChannelEquiv R FL Pl ν) = o ν := by
    simp [alive_eq_of_goodOutcome hgo, outcomeOf]
  have hdone := unitTarget_eq_done_of_mem_cur hu (hlt.trans_eq halive.symm)
  have hhold (d : Bool) : UnitId.holder (moves R FL Pl).channelParty
      (.new ν k : PlanUnit R FL Pl U0 U1) d = Pl.party ((moveChannelEquiv R FL Pl ν).1.party
        ((moveChannelEquiv R FL Pl ν).1.law.channelEnd (moveChannelEquiv R FL Pl ν).2 d)) := rfl
  have hmem (P : T.Node) (hP : IsChild P (moveChannelEquiv R FL Pl ν)) :
      (.new ν k : PlanUnit R FL Pl U0 U1) ∈ assignedUnits R FL Pl lhat n o P :=
    new_mem_assignedUnits.2 ⟨halive ▸ hlt, hP⟩
  have ho : outcomeOf R FL Pl o (moveChannelEquiv R FL Pl ν) = o ν := by simp [outcomeOf]
  simp only [hhold] at hne ⊢
  simp only [unitTarget] at hdone
  revert hgo hdone hmem ho hne
  rcases moveChannelEquiv R FL Pl ν with ⟨⟨x, hx⟩ | l, β⟩
  · intro hgo hdone hmem ho hne
    have hcount : moveCount lhat (initialCounts n) (outcomeOf R FL Pl o) (.relay x hx) ≠ 0 := by
      rw [← hgo β, ho]; omega
    have hch := channelHolders_of_target_eq_done hh hx hdone hcount
    simp only [channelHolders] at hch
    refine ⟨_, fun h0 => hne ?_, hmem _ ⟨hdone, rfl⟩, by rw [← Sym2.map_mk, hch, Sym2.map_mk]⟩
    rw [h0] at hch
    rcases Sym2.eq_iff.1 hch with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      exact congrArg Pl.party (h1.trans h2.symm)
  · intro _ hdone
    exact absurd hdone (by simp [Move.target])

/-- **The units in the end** ([AnthropicVPVNP2026], Theorem H.2(b), p. 46): for good outcomes and
if no base party has too many initial units, every unit that is current after all moves, is not
dead and joins two parties joins a party other than the root and its parent. -/
theorem exists_parent {u : PlanUnit R FL Pl U0 U1}
    (hu : u ∈ Play.cutUnits (UnitId.holder (moves R FL Pl).channelParty) id
      ((towerPlan R FL Pl lhat U0 U1).cur n o (Fintype.card (Move R ch FL)) \
        deadUnits U0 R FL Pl o)) :
    ∃ p, p ≠ Pl.party .root ∧ s(UnitId.holder (moves R FL Pl).channelParty u false,
      UnitId.holder (moves R FL Pl).channelParty u true) =
        s(p, treeParent R FL Pl hh lhat n o p) := by
  obtain ⟨hu, hne⟩ := Play.mem_cutUnits.1 hu
  obtain ⟨P, hP, -, he⟩ := exists_node_of_mem_cur hh hn hg (mem_sdiff.1 hu).1 (mem_sdiff.1 hu).2 hne
  exact ⟨Pl.party P, fun h0 => hP (Pl.party.injective h0), by simp [he, treeParent]⟩

/-- **The units between a party and its parent** ([AnthropicVPVNP2026], Theorem H.2(b), (e),
p. 46): for good outcomes and if no base party has too many initial units, the units in the end
that are not dead and join a party other than the root and its parent are at most `treeUnits`. -/
theorem card_between_le {p : Fin (A + A')} (hp : p ≠ Pl.party .root) :
    ((Play.cutUnits (UnitId.holder (moves R FL Pl).channelParty) id
        ((towerPlan R FL Pl lhat U0 U1).cur n o (Fintype.card (Move R ch FL)) \
          deadUnits U0 R FL Pl o)).filter fun u =>
        s(UnitId.holder (moves R FL Pl).channelParty u false,
          UnitId.holder (moves R FL Pl).channelParty u true) =
          s(p, treeParent R FL Pl hh lhat n o p)).card ≤ treeUnits R FL Pl lhat n o p := by
  set L := edgeLoads (load lhat (initialCounts n) (outcomeOf R FL Pl o))
  have hp' : Pl.party.symm p ≠ .root := fun h0 => hp (by rw [← h0, Equiv.apply_symm_apply])
  refine (card_le_card fun u hu => ?_).trans (card_assignedUnits_le (Pl.party.symm p))
  obtain ⟨hu, he⟩ := mem_filter.1 hu
  obtain ⟨hu, hne⟩ := Play.mem_cutUnits.1 hu
  obtain ⟨Q, hQ, hmem, he'⟩ :=
    exists_node_of_mem_cur hh hn hg (mem_sdiff.1 hu).1 (mem_sdiff.1 hu).2 hne
  rw [he, treeParent] at he'
  rcases Sym2.eq_iff.1 he' with ⟨h1, -⟩ | ⟨h1, h2⟩
  · rwa [Pl.party.symm_apply_eq.2 h1]
  · have a1 := Tower.Node.stage_parent hh L hQ
    have a2 := Tower.Node.stage_parent hh L hp'
    rw [Pl.party.injective h2] at a2
    rw [← Pl.party.symm_apply_eq.2 h1] at a1
    omega

end End

/-! ### The units between the parties and their parents -/

variable {ρ : ℝ} (hρ : StageRate FL ρ)
include hρ

private theorem treeUnits_le (p : Fin (A + A')) :
    treeUnits R FL Pl lhat n o p ≤ edgeUnitBound FL Uu A lhat ρ := by
  unfold treeUnits
  rcases Pl.party.symm p with _ | ⟨j, c⟩
  · exact Nat.zero_le _
  · exact parentUnits_le hρ (Nat.le_of_lt_succ j.2) c

/-- **The units of a party and its children** ([AnthropicVPVNP2026], Theorem H.2(e), p. 46): if
the bound `b` of the children and the chambers of the last level are at most `c`, the units
between a party and its parent and between its children and the party are at most `c + 1` times
`edgeUnitBound`. -/
theorem treeUnits_add_sum_le (hh : 0 < h) {c : ℕ} (hb : b ≤ c) (hX : Fintype.card (T.X J) ≤ c)
    (p : Fin (A + A')) :
    treeUnits R FL Pl lhat n o p + ∑ q ∈ univ.filter
        (fun q => q ≠ Pl.party .root ∧ treeParent R FL Pl hh lhat n o q = p),
      treeUnits R FL Pl lhat n o q ≤ (c + 1) * edgeUnitBound FL Uu A lhat ρ := by
  have hcard : (univ.filter fun q => q ≠ Pl.party .root ∧
      treeParent R FL Pl hh lhat n o q = p).card ≤ c := by
    rcases eq_or_ne p (Pl.party .root) with rfl | hp
    · exact (card_children_root_le hh).trans hX
    · exact (card_children_le hh hp).trans hb
  rw [add_mul, one_mul, add_comm]
  exact add_le_add ((sum_le_card_nsmul _ _ _ fun q _ => treeUnits_le hρ q).trans
    (by simpa using Nat.mul_le_mul_right _ hcard)) (treeUnits_le hρ p)

/-- **All units between the parties and their parents** ([AnthropicVPVNP2026], Theorem H.2(e),
p. 46): for `ρ < 1` they are at most `treeUnitBound`. -/
theorem sum_treeUnits_le (hρ1 : ρ < 1) :
    ∑ p, treeUnits R FL Pl lhat n o p ≤ treeUnitBound FL Uu A lhat ρ := by
  rw [← Pl.party.sum_comp]
  simp only [treeUnits, Equiv.symm_apply_apply]
  rw [← (proxy_equiv% T.Node).sum_comp, Fintype.sum_sum_type, Fintype.sum_unique, Fintype.sum_sigma]
  refine le_of_eq_of_le ?_
    (sum_parentUnits_le (n := initialCounts n) (o := outcomeOf R FL Pl o) hρ hρ1)
  rw [← Fin.sum_univ_eq_sum_range (fun j => ∑ c : T.X j, T.parentUnits _ j c)]
  exact zero_add _

omit hρ

/-! ### The units at a party -/

/-- **The layers of the law moves at a party** ([AnthropicVPVNP2026], Theorem H.2(c), p. 46): for
good outcomes and if every place is an end of a near pair, the numbers of units of the law moves
at a party are at most the units that it ever holds. -/
theorem sum_count_le_card_seenAt (hg : ∀ x, (towerPlan R FL Pl lhat U0 U1).Good n o x)
    (hnr : ∀ f : T.Fl, ∃ ν, T.cN ν = f ∨ T.dN ν = f) (p : Fin (A + A')) :
    ∑ r ∈ univ.filter (fun r : (moves R FL Pl).Role =>
        (moves R FL Pl).roleParty r = p ∧ (moveOrder R ch FL r.1).isVertex = true),
      (towerPlan R FL Pl lhat U0 U1).count n o r.1 ≤
    ((Plan.seenAt n o (Fintype.card (Move R ch FL))).filter
      (Play.Holds (UnitId.holder (moves R FL Pl).channelParty) p)).card := by
  have key (mv : Move R ch FL) (hv : mv.isVertex = true) (q : mv.law.Role) :
      ∃ c d, mv.law.channelEnd c d = q ∧ ∀ o' : MoveChannel R ch FL → ℕ,
        GoodOutcome lhat (initialCounts n) o' mv → moveCount lhat (initialCounts n) o' mv ≤
          o' ⟨mv, c⟩ := by
    rcases mv with _ | l
    · simp [Move.isVertex] at hv
    · obtain ⟨c, d, hcd⟩ := FL.exists_channelEnd hnr l.kind q
      exact ⟨c, d, hcd, fun o' hg' => hg'.2 c⟩
  rw [Plan.card_filter_holds_seenAt,
    filter_true_of_mem fun (ν : (moves R FL Pl).Channel) _ => ν.1.isLt]
  refine le_add_left ?_
  let ψ : (moves R FL Pl).Channel × Bool → (moves R FL Pl).Role :=
    fun y => ⟨y.1.1, ((moves R FL Pl).law y.1.1).channelEnd y.1.2 y.2⟩
  let S := univ.filter fun y : (moves R FL Pl).Channel × Bool =>
    (moves R FL Pl).channelParty y.1 y.2 = p ∧
      (towerPlan R FL Pl lhat U0 U1).count n o y.1.1 ≤ o y.1
  calc _ ≤ ∑ r ∈ S.image ψ, (towerPlan R FL Pl lhat U0 U1).count n o r.1 := by
        refine sum_le_sum_of_subset ?_
        rintro ⟨x, q⟩ hr
        obtain ⟨hp, hv⟩ := (mem_filter.1 hr).2
        obtain ⟨c, d, hcd, hle⟩ := key _ hv q
        refine mem_image.2 ⟨(⟨x, c⟩, d), mem_filter.2 ⟨mem_univ _, ?_, ?_⟩, ?_⟩
        · exact (congrArg ((moves R FL Pl).party x) hcd).trans hp
        · exact (hle _ (goodOutcome_of_good hg _)).trans_eq (outcomeOf_moveOrder o x c)
        · exact congrArg (Sigma.mk x) hcd
    _ ≤ ∑ y ∈ S, (towerPlan R FL Pl lhat U0 U1).count n o (ψ y).1 :=
        sum_image_le_of_nonneg fun _ _ => Nat.zero_le _
    _ ≤ ∑ y ∈ univ.filter (fun y : (moves R FL Pl).Channel × Bool =>
          (moves R FL Pl).channelParty y.1 y.2 = p), ((o y.1 : ℕ) + 1) :=
        (sum_le_sum fun y hy => (mem_filter.1 hy).2.2.trans (Nat.le_succ _)).trans
          (sum_le_sum_of_subset fun y hy => mem_filter.2 ⟨mem_univ _, (mem_filter.1 hy).2.1⟩)
    _ = _ := by rw [sum_filter, Fintype.sum_prod_type]

/-- The units at a node, its children, and the chambers of the last level at the root. -/
private theorem lift_le (hh : 0 < h) (Lf : ∀ j, T.Ed j → ℕ) (P : T.Node) :
    P.lift (fun j c => 8 * T.parentUnits Lf j c + 3 * T.childUnits hh Lf j c) (∑ e, Lf J e) ≤
      8 * (P.lift (T.parentUnits Lf) 0 + ∑ Q ∈ univ.filter (fun Q : T.Node => Q ≠ .root ∧
        Q.parent hh Lf = P), Q.lift (T.parentUnits Lf) 0) := by
  have h1 := Tower.Node.lift_childUnits_le hh Lf P
  have h2 : ∑ c, T.parentUnits Lf J c = 2 * ∑ e, Lf J e := T.sum_incidentSum (Lf J)
  cases P <;> simp only [Tower.Node.lift] at h1 ⊢ <;> omega

/-- A party has at most two ends of channels for every dead unit at it. -/
private theorem channelEndCount_le (p : Fin (A + A')) : channelEndCount R FL Pl p ≤
    2 * ((deadUnits U0 R FL Pl o).filter
      (Play.Holds (UnitId.holder (moves R FL Pl).channelParty) p)).card := by
  rw [deadUnits, filter_image, card_image_of_injective _ fun ν ν' e => (UnitId.new.inj e).1,
    card_filter, mul_sum, channelEndCount]
  refine sum_le_sum fun ν _ => ?_
  simp only [Fintype.sum_bool, Play.Holds, UnitId.holder, Bool.exists_bool]
  split_ifs <;> omega

/-- **The units that a party ever holds and reads** ([AnthropicVPVNP2026], Theorem H.2(e), p. 46,
and its proof, "For (e)", p. 48): for good outcomes, if every place is an end of a near pair,
every law has at most `Sm` slots and the base parties have at most `ℓf` initial units, the units
that a party ever holds, and those that its roles read, zeros in slots included, are at most
`8 (4 + (2 |Nr| lengthBound + 1 + Sm) |Kind|)` times the units between the party and its parent
and between its children and the party, `ℓf + 8 m lhat` more at a base party, and twice the dead
units at the party. -/
theorem card_held_add_le (hr : 0 < r) (hb : 0 < b) (hh : 0 < h)
    (hg : ∀ x, (towerPlan R FL Pl lhat U0 U1).Good n o x)
    (hnr : ∀ f : T.Fl, ∃ ν, T.cN ν = f ∨ T.dN ν = f) {Sm : ℕ}
    (hSm : ∀ d, Fintype.card (FL.law d).Slot ≤ Sm) {ℓf : ℕ}
    (hini : ∀ a, ∑ c, ((n a c : ℕ) + n c a) ≤ ℓf) (p : Fin (A + A')) :
    ((Plan.seenAt n o (Fintype.card (Move R ch FL))).filter
        (Play.Holds (UnitId.holder (moves R FL Pl).channelParty) p)).card +
        ∑ ρ ∈ univ.filter (fun ρ : (moves R FL Pl).Role => (moves R FL Pl).roleParty ρ = p),
          (1 + Fintype.card (((moves R FL Pl).law ρ.1).SlotAt ρ.2)) *
            (towerPlan R FL Pl lhat U0 U1).count n o ρ.1 ≤
      (4 + (2 * Fintype.card T.Nr * FL.lengthBound + 1 + Sm) * Fintype.card FL.Kind) * 8 *
          (treeUnits R FL Pl lhat n o p + ∑ q ∈ univ.filter
            (fun q => q ≠ Pl.party .root ∧ treeParent R FL Pl hh lhat n o q = p),
            treeUnits R FL Pl lhat n o q) +
        (if (p : ℕ) < A then ℓf + 8 * m * lhat else 0) +
        2 * ((deadUnits U0 R FL Pl o).filter
          (Play.Holds (UnitId.holder (moves R FL Pl).channelParty) p)).card := by
  obtain ⟨P, rfl⟩ := Pl.party.surjective p
  have h0 := heldCount_add_sum_roleUnits_le hr hb hh hg hnr hSm P fun a _ => hini a
  simp only [exists_base_iff (Pl := Pl)] at h0
  rw [sum_filter]
  refine h0.trans ?_
  have h1 := lift_le hh (edgeLoads (load lhat (initialCounts n) (outcomeOf R FL Pl o))) P
  rw [sum_children_eq hh]
  simp only [treeUnits, Equiv.symm_apply_apply]
  have h2 := channelEndCount_le (U0 := U0) (R := R) (FL := FL) (o := o) (Pl.party P)
  have h3 := Nat.mul_le_mul_left
    (4 + (2 * Fintype.card T.Nr * FL.lengthBound + 1 + Sm) * Fintype.card FL.Kind) h1
  linarith

end Cslib.Circuits.Arithmetic.Separation.Trees
