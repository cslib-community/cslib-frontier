/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.Play
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Groups of parties

When the joint weight of a position of the play (`Play.value`) is a product of tables of the
parties and the parties are divided into groups, the value is a sum, over the common contents of
the current units whose two holders are in different groups (the *cut* units), of the product of
the values of the groups (`Play.value_groups`). This is the step of the cutting argument of
[AnthropicVPVNP2026] (Proposition J.2; module `Nc.Cut.Groups`) that makes the pieces of a
computation independent once the contents of the cut units are fixed.

## Main definitions

* `Play.cutUnits`: the current units whose holders are in different groups.
* `Play.groupContents`, `Play.GroupAgree`: the contents of the copies at the parties of a group,
  and their agreement inside the group and with given contents of the cut units.
* `Play.groupValue`: the value of a group for given contents of the cut units.

## Main results

* `Play.value_groups`: the value of a position is a sum of products of values of groups.
* `Play.ne_empty_of_groupValue_ne_zero`: when the tables of the parties vanish on empty copies of
  the units they hold, the value of a group vanishes unless the units it shares with other groups
  are not empty.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Proposition J.2; module `Nc.Cut.Groups`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Play

open Finset

variable {F A U W G : Type*} [DecidableEq G]

/-- The current units whose two holders are in different groups. -/
def cutUnits (h : U → Bool → A) (grp : A → G) (Cur : Finset U) : Finset U :=
  {u ∈ Cur | grp (h u false) ≠ grp (h u true)}

@[simp]
theorem mem_cutUnits {h : U → Bool → A} {grp : A → G} {Cur : Finset U} {u : U} :
    u ∈ cutUnits h grp Cur ↔ u ∈ Cur ∧ grp (h u false) ≠ grp (h u true) := by
  simp [cutUnits]

variable [Fintype A] [DecidableEq A] [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W]

/-- The contents of the copies at the parties of the group `g`: only the copies of seen units at
their holders in `g` are not empty. -/
def groupContents (h : U → Bool → A) (e : W) (Seen : Finset U) (grp : A → G) (g : G) :
    Finset (A → U → W) :=
  {y | ∀ a u, ¬(grp a = g ∧ u ∈ Seen ∧ Holds h a u) → y a u = e}

@[simp]
theorem mem_groupContents {h : U → Bool → A} {e : W} {Seen : Finset U} {grp : A → G} {g : G}
    {y : A → U → W} : y ∈ groupContents h e Seen grp g ↔
      ∀ a u, ¬(grp a = g ∧ u ∈ Seen ∧ Holds h a u) → y a u = e := by
  simp [groupContents]

/-- Within the group `g`, the two copies of a current unit agree when both holders are in `g`,
and the copy in `g` is `b` when exactly one holder is. -/
structure GroupAgree (h : U → Bool → A) (grp : A → G) (g : G) (Cur : Finset U) (b : U → W)
    (y : A → U → W) : Prop where
  /-- Both holders are in the group. -/
  inner : ∀ u ∈ Cur, grp (h u false) = g → grp (h u true) = g → y (h u false) u = y (h u true) u
  /-- Exactly one holder is in the group. -/
  outer : ∀ u ∈ Cur, ∀ d, grp (h u d) = g → grp (h u !d) ≠ g → y (h u d) u = b u

instance (h : U → Bool → A) (grp : A → G) (g : G) (Cur : Finset U) (b : U → W) (y : A → U → W) :
    Decidable (GroupAgree h grp g Cur b y) :=
  decidable_of_iff
    ((∀ u ∈ Cur, grp (h u false) = g → grp (h u true) = g → y (h u false) u = y (h u true) u) ∧
      ∀ u ∈ Cur, ∀ d, grp (h u d) = g → grp (h u !d) ≠ g → y (h u d) u = b u)
    ⟨fun hh => ⟨hh.1, hh.2⟩, fun hh => ⟨hh.inner, hh.outer⟩⟩

variable [CommSemiring F]

/-- The value of the group `g` when the units shared with other groups have the contents `b`. -/
def groupValue (h : U → Bool → A) (e : W) (Seen Cur : Finset U) (grp : A → G)
    (φ : A → (U → W) → F) (g : G) (b : U → W) : F :=
  ∑ y ∈ groupContents h e Seen grp g,
    if GroupAgree h grp g Cur b y then ∏ a with grp a = g, φ a (y a) else 0

theorem groupValue_eq_sum_filter (h : U → Bool → A) (e : W) (Seen Cur : Finset U) (grp : A → G)
    (φ : A → (U → W) → F) (g : G) (b : U → W) :
    groupValue h e Seen Cur grp φ g b =
      ∑ y ∈ groupContents h e Seen grp g with GroupAgree h grp g Cur b y,
        ∏ a with grp a = g, φ a (y a) :=
  (sum_filter _ _).symm

/-- If the tables of the parties vanish unless every seen unit that the party holds is not empty,
then the value of a group vanishes unless the current units that it shares with other groups are
not empty. -/
theorem ne_empty_of_groupValue_ne_zero {h : U → Bool → A} {e : W} {Seen Cur : Finset U}
    (hCur : Cur ⊆ Seen) {grp : A → G} {φ : A → (U → W) → F} {g : G} {b : U → W}
    (hφ : ∀ a y, φ a y ≠ 0 → ∀ u ∈ Seen, Holds h a u → y u ≠ e)
    (hv : groupValue h e Seen Cur grp φ g b ≠ 0) {u : U} (hu : u ∈ Cur) {d : Bool}
    (hd : grp (h u d) = g) (hd' : grp (h u !d) ≠ g) : b u ≠ e := by
  rw [groupValue_eq_sum_filter] at hv
  obtain ⟨y, hy, hne⟩ := exists_ne_zero_of_sum_ne_zero hv
  rw [← (mem_filter.1 hy).2.outer u hu d hd hd']
  exact hφ _ _ (fun h0 => hne (prod_eq_zero (mem_filter.2 ⟨mem_univ _, hd⟩) h0)) u (hCur hu)
    (holds_end h u d)

variable [Fintype G]

/-- **Groups.** The value of a position whose weight is a product of tables of the parties is the
sum, over the common contents of the cut units, of the product of the values of the groups. -/
theorem value_groups (h : U → Bool → A) (e : W) (Seen Cur : Finset U) (grp : A → G)
    (φ : A → (U → W) → F) :
    value h e Seen Cur (fun y => ∏ a, φ a (y a)) =
      ∑ b ∈ common e (cutUnits h grp Cur), ∏ g, groupValue h e Seen Cur grp φ g b := by
  have hR (b : U → W) : ∏ g, groupValue h e Seen Cur grp φ g b =
      ∑ p ∈ Fintype.piFinset fun g => groupContents h e Seen grp g,
        if ∀ g, GroupAgree h grp g Cur b (p g) then ∏ a, φ a (p (grp a) a) else 0 := by
    simp only [groupValue]
    rw [prod_univ_sum]
    refine sum_congr rfl fun p _ => ?_
    rw [prod_ite_zero, ← prod_fiberwise univ grp]
    simp only [mem_univ, forall_true_left]
    congr 1
    exact prod_congr rfl fun g _ => prod_congr rfl fun a ha => by rw [(mem_filter.1 ha).2]
  simp only [hR]
  rw [← sum_product', ← sum_filter, value_eq_sum_filter]
  refine sum_nbij' (fun y => (fun u => if u ∈ cutUnits h grp Cur then y (h u false) u else e,
      fun g a u => if grp a = g then y a u else e)) (fun q a u => q.2 (grp a) a u) ?_ ?_ ?_ ?_ ?_
  · intro y hy
    simp only [mem_filter, mem_product, mem_contents, mem_common, Fintype.mem_piFinset,
      mem_groupContents] at hy ⊢
    refine ⟨⟨fun u hu => ite_eq_right hu, fun g a u hn => ?_⟩, fun g => ⟨?_, ?_⟩⟩ <;>
      grind [Agree, cutUnits, cases Bool]
  · rintro ⟨b, p⟩ hq
    simp only [mem_filter, mem_product, mem_contents, mem_common, Fintype.mem_piFinset,
      mem_groupContents] at hq ⊢
    grind [Agree, cutUnits, GroupAgree, cases Bool]
  · intro y hy
    funext a u
    simp
  · rintro ⟨b, p⟩ hq
    simp only [mem_filter, mem_product, mem_common, Fintype.mem_piFinset,
      mem_groupContents] at hq
    ext : 2 <;> grind [cutUnits, GroupAgree, cases Bool]
  · intro y hy
    exact prod_congr rfl fun a _ => by simp

end Cslib.Circuits.Arithmetic.Separation.Play
