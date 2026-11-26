/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.CoveringTower.Chamber
public import CslibFrontier.Foundations.Combinatorics.CoveringTower.Incident
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.DeriveFintype

/-!
# The tree of a tower

The proof of Theorem H.2 of [AnthropicVPVNP2026] gathers units in a tree whose nodes
(`Cslib.CoveringTower.Tower.Node`) are the chambers of all levels of a
`Cslib.CoveringTower.Tower` and a root. For loads `Lf` on the edges of every level, the chosen
type of a level is the first type whose edges have the least sum of the squares of their loads
(`Cslib.CoveringTower.Tower.IsChosenType`); the parent of a chamber of the level `j` is the host
of its vertex of the chosen type, a chamber of the level `j + 1`, and the units between a chamber
and its parent are the loads of the edges at the chamber. The hosts of a type are injective
below the level `J`, so a chamber has at most `b` children: at most one at every place. The
chambers of the level `J` and the root have the root as their parent (`Node.parent`), and the
units between the children of a chamber and the chamber add up the units between each child and
its parent (`childUnits`). With the stage of a node (`Node.stage`), the level of a chamber and
`J + 1` at the root, the nodes form a tree by stages.

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], modules `Nc.Tow.Net`, `Nc.Tow.Tree`,
`Nc.Tow.Ever1`, `Nc.Tow.EndB` and `Paper.Tree`.

## Main definitions

* `Cslib.CoveringTower.Tower.Node`, `Cslib.CoveringTower.Tower.Node.ofChamber`: the nodes of the
  tree.
* `Cslib.CoveringTower.Tower.Node.lift`: a function on the nodes from functions on the chambers
  of every level.
* `Cslib.CoveringTower.Tower.sqLoad`, `Cslib.CoveringTower.Tower.IsChosenType`: the sum of the
  squares of the loads of the edges of a type, and the types that are chosen for the loads of the
  edges of a level.
* `Cslib.CoveringTower.Tower.chosenType`, `Cslib.CoveringTower.Tower.parentChamber`,
  `Cslib.CoveringTower.Tower.parentUnits`: the chosen type of a level, the parent of a chamber,
  and the units between a chamber and its parent.
* `Cslib.CoveringTower.Tower.childUnits`, `Cslib.CoveringTower.Tower.Node.parent`: the units
  between the children of a chamber and the chamber, and the parent of a node.
* `Cslib.CoveringTower.Tower.Node.stage`: the stage of a node, its level, and `J + 1` at the
  root.

## Main results

* `Cslib.CoveringTower.Tower.isChosenType_chosenType`,
  `Cslib.CoveringTower.Tower.isChosenType_iff`: the chosen type is the one type that is chosen.
* `Cslib.CoveringTower.Tower.IsChosenType.mul_sum_sq_le`: the edges of a chosen type carry at most
  the average of the sums of the squares of the loads of the types.
* `Cslib.CoveringTower.Tower.card_children`: a chamber has at most `b` children.
* `Cslib.CoveringTower.Tower.Node.sum_ofChamber_castSucc`,
  `Cslib.CoveringTower.Tower.Node.sum_ofChamber_succ`: `Node.lift` at a node by the chambers of
  the levels below `J` and of the level `J`, and of the level `0` and of the levels above it.
* `Cslib.CoveringTower.Tower.sum_ite_childUnits`: the units between the children of the chambers
  with a property and these chambers, by the chambers whose parents have the property.
* `Cslib.CoveringTower.Tower.Node.stage_parent`, `Cslib.CoveringTower.Tower.Node.stage_eq_iff`:
  the parent of a node other than the root is in the next stage, and only the root is in the
  stage `J + 1`.
* `Cslib.CoveringTower.Tower.Node.card_children_le`,
  `Cslib.CoveringTower.Tower.Node.card_children_root_le`,
  `Cslib.CoveringTower.Tower.Node.lift_childUnits_le`: a node other than the root has at most `b`
  children and the root at most the chambers of the level `J`, and the units between the children
  of a node and the node.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Theorem H.2(a), p. 45, Theorem H.2(e), p. 46, and the proof ("One stage" and "Bounds", p. 47;
  "For (e)", p. 48); modules `Nc.Tow.Net`, `Nc.Tow.Tree`, `Nc.Tow.Ever1`, `Nc.Tow.EndB`,
  `Paper.Tree`
-/

public section

namespace Cslib.CoveringTower.Tower

open Finset

variable {h b D J r : ℕ}

/-- The nodes of the tree: the root, and the chambers of all levels of the tower. -/
inductive Node (T : Tower h b D J r) where
  /-- The root. -/
  | root
  /-- A chamber of the level `j`. -/
  | chamber (j : Fin (J + 1)) (c : T.X j)
  deriving DecidableEq, Fintype

variable {T : Tower h b D J r} {j j' : ℕ}

namespace Node

/-- The node of a chamber of the level `j ≤ J`. -/
@[expose] def ofChamber (hj : j ≤ J) (c : T.X j) : T.Node := .chamber ⟨j, Nat.lt_succ_of_le hj⟩ c

@[simp]
theorem ofChamber_inj {hj hj' : j ≤ J} {c c' : T.X j} :
    ofChamber hj c = ofChamber hj' c' ↔ c = c' := by
  simp [ofChamber]

theorem ofChamber_ne_of_ne (hjj : j ≠ j') {hj : j ≤ J} {hj' : j' ≤ J} {c : T.X j} {c' : T.X j'} :
    ofChamber hj c ≠ ofChamber hj' c' := by
  simp [ofChamber, hjj]

@[simp]
theorem ofChamber_ne_root {hj : j ≤ J} {c : T.X j} : ofChamber hj c ≠ root := by
  simp [ofChamber]

/-- A function on the nodes from a function on the chambers of every level and a value at the
root. -/
@[expose] def lift {α : Type*} (f : ∀ j, T.X j → α) (a : α) : T.Node → α
  | .root => a
  | .chamber j c => f j c

/-- The value of `Node.lift` at a chamber. -/
@[simp]
theorem lift_ofChamber {α : Type*} (f : ∀ j, T.X j → α) (a : α) (hj : j ≤ J) (c : T.X j) :
    (ofChamber hj c).lift f a = f j c :=
  rfl

variable {M : Type*} [AddCommMonoid M]

/-- The values of `g` at the chambers of all levels that are the node `P`. -/
private theorem sum_chamber_ite (g : ∀ j, T.X j → M) (P : T.Node) :
    ∑ j : Fin (J + 1), ∑ c : T.X j, (if chamber j c = P then g j c else 0) = P.lift g 0 := by
  cases P with
  | root => simp [lift]
  | chamber k c =>
    rw [Fintype.sum_eq_single k fun j hj => sum_eq_zero fun c' _ => by simp [hj]]
    simp [lift]

/-- The values of `g` at the chambers of the levels below `J` and of the level `J` that are the
node `P`. -/
theorem sum_ofChamber_castSucc (g : ∀ j, T.X j → M) (P : T.Node) :
    (∑ j : Fin J, ∑ c : T.X j, if ofChamber j.2.le c = P then g j c else 0) +
      ∑ c : T.X J, (if ofChamber le_rfl c = P then g J c else 0) = P.lift g 0 :=
  (Fin.sum_univ_castSucc _).symm.trans (sum_chamber_ite g P)

/-- The values of `g` at the chambers of the level `0` and of the levels above it that are the
node `P`. -/
theorem sum_ofChamber_succ (g : ∀ j, T.X j → M) (P : T.Node) :
    (∑ c : T.X 0, if ofChamber (Nat.zero_le J) c = P then g 0 c else 0) +
      ∑ j : Fin J, ∑ c : T.X (j + 1), (if ofChamber j.2 c = P then g (j + 1) c else 0) =
      P.lift g 0 :=
  (Fin.sum_univ_succ _).symm.trans (sum_chamber_ite g P)

end Node

variable (T) in
/-- The sum of the squares of the loads `l` of the edges of the type `i` of a level. -/
@[expose] def sqLoad {j : ℕ} (l : T.Ed j → ℕ) (i : Fin h) : ℕ :=
  ∑ e : T.Ed j, if T.ty e = i then l e ^ 2 else 0

variable (T) in
/-- The type `i` is chosen for the loads `l` of the edges of a level: it is the first type whose
edges have the least sum of the squares of their loads. -/
@[expose] def IsChosenType {j : ℕ} (l : T.Ed j → ℕ) (i : Fin h) : Prop :=
  IsLeast {i | ∀ i', T.sqLoad l i ≤ T.sqLoad l i'} i

instance {j : ℕ} (l : T.Ed j → ℕ) (i : Fin h) : Decidable (T.IsChosenType l i) :=
  inferInstanceAs (Decidable ((∀ i', T.sqLoad l i ≤ T.sqLoad l i') ∧
    ∀ ⦃a⦄, (∀ i', T.sqLoad l a ≤ T.sqLoad l i') → i ≤ a))

/-- The edges of a chosen type have at most the average of the sums of the squares of the loads
of the edges of each type. -/
theorem IsChosenType.mul_sum_sq_le {j : ℕ} {l : T.Ed j → ℕ} {i : Fin h}
    (hi : T.IsChosenType l i) :
    (h : ℝ) * ∑ e ∈ univ.filter (T.ty · = i), (l e : ℝ) ^ 2 ≤ ∑ e, (l e : ℝ) ^ 2 := by
  have h1 : h * T.sqLoad l i ≤ ∑ e, l e ^ 2 := calc
    h * T.sqLoad l i = ∑ _i' : Fin h, T.sqLoad l i := by simp
    _ ≤ ∑ i', T.sqLoad l i' := sum_le_sum fun i' _ => hi.1 i'
    _ = _ := by
      simp only [sqLoad]
      rw [sum_comm]
      simp
  rw [sqLoad, ← sum_filter] at h1
  exact_mod_cast h1

private theorem nonempty_minimizers (hh : 0 < h) {j : ℕ} (l : T.Ed j → ℕ) :
    (univ.filter fun i : Fin h => ∀ i', T.sqLoad l i ≤ T.sqLoad l i').Nonempty := by
  obtain ⟨i, -, hi⟩ := exists_min_image univ (T.sqLoad l) ⟨⟨0, hh⟩, mem_univ _⟩
  exact ⟨i, mem_filter.2 ⟨mem_univ _, fun i' => hi i' (mem_univ _)⟩⟩

variable (T) (hh : 0 < h) (Lf : ∀ j, T.Ed j → ℕ)

/-- The chosen type at the level `j` for the loads `Lf` on the edges (`IsChosenType`): the first
type whose edges have the least sum of the squares of their loads. -/
noncomputable def chosenType (j : ℕ) : Fin h :=
  (univ.filter fun i : Fin h => ∀ i', T.sqLoad (Lf j) i ≤ T.sqLoad (Lf j) i').min'
    (nonempty_minimizers hh (Lf j))

/-- The parent of a chamber of the level `j`: the host of its vertex of the chosen type. -/
@[expose] noncomputable def parentChamber {j : ℕ} (c : T.X j) : T.X (j + 1) :=
  T.hostOf (T.chosenType hh Lf j) c

/-- The units between a chamber of the level `j` and its parent: the loads of the edges at the
chamber. -/
abbrev parentUnits (j : ℕ) (c : T.X j) : ℕ := T.incidentSum (Lf j) c

variable {T}

/-- The chosen type is chosen. -/
theorem isChosenType_chosenType (j : ℕ) : T.IsChosenType (Lf j) (T.chosenType hh Lf j) :=
  ⟨(mem_filter.1 (min'_mem _ _)).2, fun _ hi => min'_le _ _ (mem_filter.2 ⟨mem_univ _, hi⟩)⟩

variable {Lf} in
/-- A type is chosen exactly when it is the chosen type. -/
theorem isChosenType_iff {j : ℕ} {i : Fin h} :
    T.IsChosenType (Lf j) i ↔ i = T.chosenType hh Lf j :=
  ⟨fun hi => hi.unique (isChosenType_chosenType hh Lf j),
    fun hi => hi ▸ isChosenType_chosenType hh Lf j⟩

/-- A chamber of a level `j + 1 ≤ J` has at most `b` children. -/
theorem card_children {j : ℕ} (hj : j < J) (c' : T.X (j + 1)) :
    (univ.filter fun c : T.X j => T.parentChamber hh Lf c = c').card ≤ b := by
  refine (card_le_card_of_injOn (T.co (T.chosenType hh Lf j)) (fun _ _ => mem_univ _)
    fun c hc c₁ hc₁ hco => ?_).trans (card_univ.trans T.card_fl).le
  simp only [coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at hc hc₁
  exact (T.vx_co hj.le _).1 (Prod.ext (T.host_inj hj _ (hc.trans hc₁.symm)) hco)

variable (T) in
/-- The units between the children of a chamber and the chamber, for the loads `Lf` on the
edges: the units between each chamber of the level below whose parent it is and its parent;
`0` at the level `0`. -/
@[expose] noncomputable def childUnits : ∀ j, T.X j → ℕ
  | 0, _ => 0
  | j + 1, c => ∑ c' ∈ univ.filter (T.parentChamber hh Lf · = c), T.parentUnits Lf j c'

/-- The units between the children of the chambers with a property and these chambers are those
between the chambers whose parents have the property and their parents. -/
theorem sum_ite_childUnits {j : ℕ} (p : T.X (j + 1) → Prop) [DecidablePred p] :
    ∑ c, (if p c then T.childUnits hh Lf (j + 1) c else 0) =
      ∑ c : T.X j, if p (T.parentChamber hh Lf c) then T.parentUnits Lf j c else 0 := by
  simp only [childUnits, ite_sum_zero]
  exact (sum_congr rfl fun c _ => sum_congr rfl fun c' hc' => by
    rw [(mem_filter.1 hc').2]).trans (sum_fiberwise_of_maps_to (fun _ _ => mem_univ _) _)

/-- The parent of a node in the tree for the loads `Lf` on the edges: the parent chamber of a
chamber of a level below `J`, and the root for a chamber of the level `J` and for the root. -/
@[expose] noncomputable def Node.parent : T.Node → T.Node
  | .root => .root
  | .chamber j c =>
    if hj : (j : ℕ) + 1 ≤ J then .ofChamber hj (T.parentChamber hh Lf c) else .root

namespace Node

/-- The stage of a node: the level of a chamber, and `J + 1` at the root. -/
@[expose] def stage : T.Node → ℕ := lift (fun j _ => j) (J + 1)

theorem stage_le (P : T.Node) : P.stage ≤ J + 1 := by
  cases P with
  | root => exact le_rfl
  | chamber j c => exact j.2.le

/-- Only the root is of the stage `J + 1`. -/
theorem stage_eq_iff {P : T.Node} : P.stage = J + 1 ↔ P = root := by
  cases P with
  | root => exact iff_of_true rfl rfl
  | chamber j c => exact iff_of_false j.2.ne (by simp)

/-- The parent of a node other than the root is in the next stage. -/
theorem stage_parent {P : T.Node} (hP : P ≠ root) : (P.parent hh Lf).stage = P.stage + 1 := by
  cases P with
  | root => exact absurd rfl hP
  | chamber j c =>
    simp only [parent]
    split_ifs with hj
    · rfl
    · exact (congrArg (· + 1) (Nat.eq_of_lt_succ_of_not_lt j.2 (by omega))).symm

/-- The children of the root are the chambers of the level `J`. -/
private theorem filter_parent_eq_root :
    univ.filter (fun Q : T.Node => Q ≠ root ∧ Q.parent hh Lf = root) =
      univ.image (ofChamber (T := T) le_rfl) := by
  ext Q
  simp only [mem_filter, mem_univ, true_and, mem_image]
  refine ⟨fun ⟨hQ, hp⟩ => ?_, ?_⟩
  · obtain _ | ⟨⟨j, hj⟩, c⟩ := Q
    · exact absurd rfl hQ
    · have := (stage_parent hh Lf hQ).symm.trans (congrArg stage hp)
      simp only [stage, lift, add_left_inj] at this
      subst this
      exact ⟨c, rfl⟩
  · rintro ⟨c, rfl⟩
    exact ⟨ofChamber_ne_root, by simp [parent, ofChamber]⟩

/-- The children of a chamber of the level `j + 1` are the chambers of the level `j` whose parent
chamber it is. -/
private theorem filter_parent_eq_ofChamber (hj : j + 1 ≤ J) (c : T.X (j + 1)) :
    univ.filter (fun Q : T.Node => Q ≠ root ∧ Q.parent hh Lf = ofChamber hj c) =
      (univ.filter (T.parentChamber hh Lf · = c)).image (ofChamber (by omega)) := by
  ext Q
  simp only [mem_filter, mem_univ, true_and, mem_image]
  refine ⟨fun ⟨hQ, hp⟩ => ?_, ?_⟩
  · obtain _ | ⟨⟨i, hi⟩, c'⟩ := Q
    · exact absurd rfl hQ
    · have := (stage_parent hh Lf hQ).symm.trans (congrArg stage hp)
      simp only [stage, lift, ofChamber, add_left_inj] at this
      subst this
      simp only [parent, hj, dite_true] at hp
      exact ⟨c', ofChamber_inj.1 hp, rfl⟩
  · rintro ⟨c', hc', rfl⟩
    exact ⟨ofChamber_ne_root, by simp [parent, ofChamber, hj, hc']⟩

/-- A chamber of the level `0` has no children. -/
private theorem filter_parent_eq_ofChamber_zero (c : T.X 0) :
    univ.filter (fun Q : T.Node => Q ≠ root ∧ Q.parent hh Lf = ofChamber (Nat.zero_le J) c) =
      ∅ :=
  filter_false_of_mem fun Q _ ⟨hQ, hp⟩ => by
    have := (stage_parent hh Lf hQ).symm.trans (congrArg stage hp)
    simp [stage, lift, ofChamber] at this

/-- A node other than the root has at most `b` children. -/
theorem card_children_le {P : T.Node} (hP : P ≠ root) :
    (univ.filter fun Q => Q ≠ root ∧ Q.parent hh Lf = P).card ≤ b := by
  obtain _ | ⟨⟨_ | j, hj⟩, c⟩ := P
  · exact absurd rfl hP
  · exact (filter_parent_eq_ofChamber_zero hh Lf c).symm ▸ Nat.zero_le b
  · exact (filter_parent_eq_ofChamber hh Lf (j := j) (by omega) c).symm ▸
      card_image_le.trans (card_children hh Lf (by omega) c)

/-- The root has a child for every chamber of the level `J`. -/
theorem card_children_root_le :
    (univ.filter fun Q => Q ≠ root ∧ Q.parent hh Lf = root).card ≤ Fintype.card (T.X J) :=
  (filter_parent_eq_root hh Lf).symm ▸ card_image_le

/-- The units between the children of a chamber and the chamber, and at the root those between
the chambers of the level `J` and the root, are at most the units between the children of the
node and the node. -/
theorem lift_childUnits_le (P : T.Node) :
    P.lift (T.childUnits hh Lf) (∑ c, T.parentUnits Lf J c) ≤
      ∑ Q ∈ univ.filter (fun Q => Q ≠ root ∧ Q.parent hh Lf = P), Q.lift (T.parentUnits Lf) 0 := by
  obtain _ | ⟨⟨_ | j, hj⟩, c⟩ := P
  · rw [filter_parent_eq_root, sum_image fun _ _ _ _ h => ofChamber_inj.1 h]
    rfl
  · exact Nat.zero_le _
  · rw [show chamber ⟨j + 1, hj⟩ c = ofChamber (by omega) c from rfl,
      filter_parent_eq_ofChamber hh Lf (j := j) (by omega) c,
      sum_image fun _ _ _ _ h => ofChamber_inj.1 h]
    rfl

end Node

end Cslib.CoveringTower.Tower
