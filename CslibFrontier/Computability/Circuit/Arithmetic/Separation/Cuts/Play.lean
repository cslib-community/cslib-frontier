/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Positions of the play and one move

The cutting argument of [AnthropicVPVNP2026] (Appendices H.2 and J; module `Nc.Cut.Play`) rewrites
the value of a computation as a sum over what is written on *units* that are shared by *parties*.
Every unit `u` has two ends, at the parties `h u false` and `h u true`, and each end carries a
copy of the unit. *Contents* `y : A → U → W` give the copy `y a u` of the unit `u` at the party
`a`; copies of units that have not been seen, or at parties that do not hold them, are *empty* (a
fixed `e : W`).

The *value* of a position (`Play.value`) is the sum, over all contents of the units seen so far,
of a joint weight, restricted to the contents in which the two copies of every *current* unit
agree. For a weight that is a product of tables of the parties and with all seen units current,
this is the contraction of a tensor network with a party at each vertex and a unit on each edge;
here some seen units are no longer current, so their two copies are summed independently, and the
weight need not be a product.

A *move* (`Play.value_move`) takes some current units away and replaces the condition that their
copies agree by a sum, over outcomes, of tables that also read new units.

## Main definitions

* `Play.Holds`, `Play.contents`, `Play.Agree`, `Play.value`: holders of a unit, the contents of
  seen units, agreement of the copies of current units, and the value of a position.
* `Play.extend`, `Play.common`: writing common contents of new units into the copies of their
  holders.

## Main results

* `Play.sum_contents_union`: contents of old and new units whose new copies agree are contents of
  the old units together with common contents of the new ones.
* `Play.value_move`: one move.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Appendices H.2 and J; module `Nc.Cut.Play`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Play

open Finset

variable {F A U W O : Type*}

/-- The party `a` holds the unit `u`: it is at one of the two ends of `u`. -/
@[expose] def Holds (h : U → Bool → A) (a : A) (u : U) : Prop := ∃ d, h u d = a

instance [DecidableEq A] (h : U → Bool → A) (a : A) (u : U) : Decidable (Holds h a u) :=
  inferInstanceAs (Decidable (∃ d, h u d = a))

theorem holds_end (h : U → Bool → A) (u : U) (d : Bool) : Holds h (h u d) u := ⟨d, rfl⟩

/-- The copies of all units in `Cur` agree. -/
@[expose] def Agree (h : U → Bool → A) (Cur : Finset U) (y : A → U → W) : Prop :=
  ∀ u ∈ Cur, y (h u false) u = y (h u true) u

instance [DecidableEq W] (h : U → Bool → A) (Cur : Finset U) (y : A → U → W) :
    Decidable (Agree h Cur y) :=
  inferInstanceAs (Decidable (∀ u ∈ Cur, y (h u false) u = y (h u true) u))

theorem agree_union [DecidableEq U] {h : U → Bool → A} {S T : Finset U} {y : A → U → W} :
    Agree h (S ∪ T) y ↔ Agree h S y ∧ Agree h T y := by
  simp only [Agree, mem_union, or_imp, forall_and]

theorem Agree.mono {h : U → Bool → A} {S T : Finset U} {y : A → U → W} (hST : S ⊆ T)
    (hy : Agree h T y) : Agree h S y := fun u hu => hy u (hST hu)

section Contents

variable [Fintype A] [DecidableEq A] [Fintype U] [DecidableEq U] [Fintype W]
  [DecidableEq W]

/-- The contents in which only the copies of seen units at their holders are not empty. -/
def contents (h : U → Bool → A) (e : W) (Seen : Finset U) : Finset (A → U → W) :=
  {y | ∀ a u, ¬(u ∈ Seen ∧ Holds h a u) → y a u = e}

/-- Common contents of units: empty outside `New`. -/
def common (e : W) (New : Finset U) : Finset (U → W) := {z | ∀ u ∉ New, z u = e}

@[simp]
theorem mem_contents {h : U → Bool → A} {e : W} {Seen : Finset U} {y : A → U → W} :
    y ∈ contents h e Seen ↔ ∀ a u, ¬(u ∈ Seen ∧ Holds h a u) → y a u = e := by
  simp [contents]

@[simp]
theorem mem_common {e : W} {New : Finset U} {z : U → W} :
    z ∈ common e New ↔ ∀ u ∉ New, z u = e := by
  simp [common]

/-- Without units, the only common contents are empty. -/
@[simp]
theorem common_empty (e : W) : common e (∅ : Finset U) = {fun _ => e} := by
  ext z
  simp [funext_iff]

end Contents

/-- Write common contents `z` of the units in `New` into the copies of their holders. -/
@[expose] def extend [DecidableEq A] [DecidableEq U] (h : U → Bool → A) (New : Finset U)
    (y : A → U → W) (z : U → W) : A → U → W :=
  fun a u => if u ∈ New ∧ Holds h a u then z u else y a u

section Extend

variable [DecidableEq A] [DecidableEq U] {h : U → Bool → A} {New : Finset U} {y : A → U → W}
  {z : U → W} {a : A} {u : U}

theorem extend_of_holds (hu : u ∈ New) (ha : Holds h a u) : extend h New y z a u = z u :=
  ite_eq_left ⟨hu, ha⟩

theorem extend_of_notMem (hu : u ∉ New) : extend h New y z a u = y a u :=
  ite_eq_right fun hh => hu hh.1

/-- Writing no units changes nothing. -/
@[simp]
theorem extend_empty (h : U → Bool → A) (y : A → U → W) (z : U → W) : extend h ∅ y z = y := by
  funext a u
  simp [extend]

/-- Writing new units does not change whether the copies of other units agree. -/
theorem agree_extend {S : Finset U} (hd : Disjoint S New) (y : A → U → W) (z : U → W) :
    Agree h S (extend h New y z) ↔ Agree h S y :=
  forall₂_congr fun u hu => by
    rw [extend_of_notMem (disjoint_left.1 hd hu), extend_of_notMem (disjoint_left.1 hd hu)]

end Extend

variable [Fintype A] [DecidableEq A] [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W]

/-- The value of a position: the sum of the joint weight `E` over the contents of the seen units
in which the two copies of every current unit agree. -/
def value [AddCommMonoid F] (h : U → Bool → A) (e : W) (Seen Cur : Finset U)
    (E : (A → U → W) → F) : F :=
  ∑ y ∈ contents h e Seen, if Agree h Cur y then E y else 0

theorem value_eq_sum_filter [AddCommMonoid F] (h : U → Bool → A) (e : W) (Seen Cur : Finset U)
    (E : (A → U → W) → F) :
    value h e Seen Cur E = ∑ y ∈ contents h e Seen with Agree h Cur y, E y :=
  (sum_filter _ _).symm

/-- Contents of the units in `Seen ∪ New` in which the copies of the new units agree are contents
of the units in `Seen` together with common contents of the new units. -/
theorem sum_contents_union [AddCommMonoid F] (h : U → Bool → A) (e : W) {Seen New : Finset U}
    (hd : Disjoint Seen New) (f : (A → U → W) → F) :
    (∑ y ∈ contents h e (Seen ∪ New), if Agree h New y then f y else 0) =
      ∑ y ∈ contents h e Seen, ∑ z ∈ common e New, f (extend h New y z) := by
  have key : ∀ y ∈ {y ∈ contents h e (Seen ∪ New) | Agree h New y},
      extend h New (fun a u => if u ∈ New then e else y a u)
        (fun u => if u ∈ New then y (h u false) u else e) = y := by
    intro y hy
    simp only [mem_filter, mem_contents, mem_union] at hy
    funext a u
    grind [Agree, extend, Holds, cases Bool]
  rw [← sum_filter, ← sum_product']
  refine sum_nbij' (fun y => (fun a u => if u ∈ New then e else y a u,
      fun u => if u ∈ New then y (h u false) u else e)) (fun p => extend h New p.1 p.2)
    ?_ ?_ key ?_ fun y hy => by rw [key y hy]
  · intro y hy
    simp only [mem_filter, mem_product, mem_contents, mem_common, mem_union] at hy ⊢
    grind
  · rintro ⟨y, z⟩ hp
    simp only [mem_filter, mem_product, mem_contents, mem_common, mem_union] at hp ⊢
    grind [Agree, extend, Holds]
  · rintro ⟨y, z⟩ hp
    simp only [mem_product, mem_contents, mem_common] at hp
    ext a u <;> grind [extend, Holds, Finset.disjoint_left]

/-- **One move.** Some current units `Out` are taken away. If, wherever the weight `E` is not
zero, the condition that their copies agree is a sum over outcomes `o` and over common contents
of new units of tables `C o`, then the value of the position is the sum over the outcomes of the
values of the positions with the units `Out` replaced by the new ones and the weight multiplied
by the table. -/
theorem value_move [Semiring F] [Fintype O] (h : U → Bool → A) (e : W) {Seen Cur Out : Finset U}
    (hOut : Out ⊆ Cur) (hCur : Cur ⊆ Seen) (New : O → Finset U)
    (hNew : ∀ o, Disjoint Seen (New o)) (E : (A → U → W) → F)
    (hE : ∀ o y z, E (extend h (New o) y z) = E y) (C : O → (A → U → W) → F)
    (hC : ∀ y ∈ contents h e Seen, E y ≠ 0 → (if Agree h Out y then (1 : F) else 0) =
      ∑ o, ∑ z ∈ common e (New o), C o (extend h (New o) y z)) :
    value h e Seen Cur E =
      ∑ o, value h e (Seen ∪ New o) (Cur \ Out ∪ New o) fun y => E y * C o y := by
  have hstep (o : O) : value h e (Seen ∪ New o) (Cur \ Out ∪ New o) (fun y => E y * C o y) =
      ∑ y ∈ contents h e Seen, if Agree h (Cur \ Out) y then
        E y * ∑ z ∈ common e (New o), C o (extend h (New o) y z) else 0 := by
    have hd : Disjoint (Cur \ Out) (New o) := (hNew o).mono_left (sdiff_subset.trans hCur)
    simp_rw [value, agree_union, and_comm (a := Agree h (Cur \ Out) _), ite_and]
    rw [sum_contents_union h e (hNew o)]
    refine sum_congr rfl fun y _ => ?_
    simp_rw [agree_extend hd, hE]
    split_ifs <;> simp [mul_sum]
  simp_rw [hstep, value]
  rw [sum_comm]
  refine sum_congr rfl fun y hy => ?_
  have hag : Agree h Cur y ↔ Agree h (Cur \ Out) y ∧ Agree h Out y := by
    rw [← agree_union, sdiff_union_of_subset hOut]
  by_cases hE0 : E y = 0
  · simp [hE0]
  by_cases hb : Agree h (Cur \ Out) y
  · simp only [hb, ite_true, ← mul_sum, ← hC y hy hE0, hag, true_and, mul_ite, mul_one, mul_zero]
  · simp [hb, hag]

end Cslib.Circuits.Arithmetic.Separation.Play
