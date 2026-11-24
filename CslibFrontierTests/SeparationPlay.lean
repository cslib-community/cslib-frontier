/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.Groups
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators

/-! Tests of the play, as a client that sees only the public statements.

* The hypotheses of `Play.value_move` hold for the simplest move, which cuts one current unit by
  summing over its common content.
* `Play.value_groups` with all parties in one group has no cut unit, so the value of the position
  is the value of that group.
* For two parties that share one unit, where one of them also holds a unit with both ends,
  `Play.value_groups` with each party in its own group cuts only the shared unit, and the values
  of the two groups vanish unless its common content is not empty. -/

@[expose] public section

namespace CslibFrontierTests.SeparationPlay

open Finset Cslib.Circuits.Arithmetic.Separation.Play

variable {F A U W : Type} [Fintype A] [DecidableEq A] [Fintype U] [DecidableEq U] [Fintype W]
  [DecidableEq W]

/-- Cutting one current unit `u`, with no new units: the condition that its two copies agree is
the sum, over a content `o`, of the table "both copies are `o`". -/
example [Semiring F] (h : U → Bool → A) (e : W) {Seen Cur : Finset U} {u : U} (hu : u ∈ Cur)
    (hCur : Cur ⊆ Seen) (E : (A → U → W) → F) :
    value h e Seen Cur E = ∑ o : W, value h e Seen (Cur \ {u}) fun y =>
      E y * if y (h u false) u = o ∧ y (h u true) u = o then 1 else 0 := by
  have key := value_move h e (singleton_subset_iff.2 hu) hCur (fun _ : W => ∅)
    (fun _ => disjoint_empty_right _) E (fun _ y z => by rw [extend_empty])
    (fun o y => if y (h u false) u = o ∧ y (h u true) u = o then 1 else 0)
    (fun y _ _ => by
      simp only [common_empty, sum_singleton, extend_empty, Agree, mem_singleton, forall_eq]
      by_cases hy : y (h u false) u = y (h u true) u
      · simp [hy]
      · have hne : ∀ o, ¬(y (h u false) u = o ∧ y (h u true) u = o) :=
          fun o ho => hy (ho.1.trans ho.2.symm)
        simp [hy, hne])
  simpa using key

/-- With all parties in one group no unit is cut, and the value of the position is the value of
the group. -/
example [CommSemiring F] (h : U → Bool → A) (e : W) (Seen Cur : Finset U)
    (φ : A → (U → W) → F) :
    value h e Seen Cur (fun y => ∏ a, φ a (y a)) =
      groupValue h e Seen Cur (fun _ => ()) φ () fun _ => e := by
  have hcut : cutUnits h (fun _ : A => ()) Cur = ∅ := by
    ext u
    simp
  simp [value_groups h e Seen Cur (fun _ => ()) φ, hcut]

/-- Two parties and two units: the unit `false` has its ends at the two parties, and both ends of
the unit `true` are at the party `true`. -/
def ends (u d : Bool) : Bool := u || d

/-- With each party in its own group, only the shared unit is cut. -/
example : cutUnits ends id univ = {false} := by
  ext u
  cases u <;> simp [ends]

/-- The value is then a sum over the common content of the shared unit of the product of the
values of the two parties. -/
example [CommSemiring F] (e : W) (φ : Bool → (Bool → W) → F) :
    value ends e univ univ (fun y => ∏ a, φ a (y a)) =
      ∑ b ∈ common e {false}, groupValue ends e univ univ id φ true b *
        groupValue ends e univ univ id φ false b := by
  have hcut : cutUnits ends id univ = {false} := by
    ext u
    cases u <;> simp [ends]
  rw [value_groups ends e univ univ id φ, hcut]
  exact sum_congr rfl fun b _ => Fintype.prod_bool _

/-- If the tables vanish on an empty copy of a unit that the party holds, the value of each party
vanishes unless the content of the shared unit is not empty. -/
example [CommSemiring F] (e : W) (φ : Bool → (Bool → W) → F)
    (hφ : ∀ a y, φ a y ≠ 0 → ∀ u ∈ univ, Holds ends a u → y u ≠ e) (a : Bool) (b : Bool → W)
    (hv : groupValue ends e univ univ id φ a b ≠ 0) : b false ≠ e := by
  refine ne_empty_of_groupValue_ne_zero (subset_refl _) hφ hv (mem_univ false) (d := a) ?_ ?_ <;>
    cases a <;> simp [ends]

end CslibFrontierTests.SeparationPlay
