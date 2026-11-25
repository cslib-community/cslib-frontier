/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.MoveIdentity
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.PlayMoves
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators

/-! Tests of the moves of a plan, as a client that sees only the public statements.

Two parties make one move with the *equality law*, whose two roles share one slot and one
channel. The plan gives the units of the string from the party `0` to the party `1` at the slot.

* The plan obeys the rules `Cut.Plan.Ok`, so the rules can hold.
* After the move, the units of that string are no longer current, and the new units of the
  channel are (`Cut.Plan.cur_succ`).
* `Cut.Plan.value_moves` writes the value of the position at the beginning as the sum, over the
  outcomes of the move, of the values of the positions after it.
* `Cut.move_identity` for this move, when no unit is given and the move uses no units. -/

set_option linter.privateModule false

namespace CslibFrontierTests.SeparationMoves

open Finset Cslib Cslib.Circuits.Arithmetic.Separation Cslib.Circuits.Arithmetic.Separation.Cut

variable {F : Type} [CommSemiring F] {U0 U1 ub : ℕ}

/-- The equality law: the roles are `false` and `true`, with one slot and one channel between
them. There is one index, and the string on the channel is one bit. The table of a role is `1`
when its copy of the bit of the slot is the bit on the channel. -/
def equalityLaw (F : Type) [CommSemiring F] : Law F where
  Role := Bool
  Slot := Unit
  Channel := Unit
  Index := Unit
  slotEnd _ d := d
  slotEnd_ne _ := by decide
  channelEnd _ d := d
  channelEnd_ne _ := by decide
  labelLength := 0
  label _ := Fin.elim0
  label_injective _ _ _ := rfl
  length _ _ := 1
  table p _ x g := if x ⟨(), p, rfl⟩ = g ⟨(), p, rfl⟩ 0 then 1 else 0
  identity X := by
    rw [Fintype.sum_unique, ← ((Equiv.funUnique Unit (BitString 1)).trans
      (Equiv.funUnique (Fin 1) Bool)).symm.sum_comp, Fintype.sum_bool]
    have hg (b : Bool) : ((Equiv.funUnique Unit (BitString 1)).trans
        (Equiv.funUnique (Fin 1) Bool)).symm b () 0 = b := rfl
    simp only [Fintype.prod_bool, hg]
    rcases Bool.eq_false_or_eq_true (X false ()) with hf | hf <;>
      rcases Bool.eq_false_or_eq_true (X true ()) with ht | ht <;> simp [hf, ht]
  connected _ _ _ _ := rfl

/-- One move with the equality law: the role `false` is the party `0` and the role `true` is the
party `1`. There are no extra parties. -/
def moves (F : Type) [CommSemiring F] : Moves F (2 + 0) 1 where
  law _ := equalityLaw F
  party _ (d : Bool) := if d then 1 else 0
  party_injective _ := by
    rintro (_ | _) (_ | _) h <;> first | rfl | simp at h

/-- The plan that gives all units of the string from the party `0` to the party `1` at the slot
of the move. The move uses `U0` units, and all outcomes are allowed. -/
def plan (F : Type) [CommSemiring F] (U0 U1 : ℕ) : Plan (moves F) U0 U1 where
  given n _ _ := (univ.filter fun k : Fin U0 => (k : ℕ) < n 0 1).image (UnitId.init 0 1)
  count _ _ _ := U0
  Good _ _ _ := True

instance (n : Fin 2 → Fin 2 → Fin (U0 + 1)) (o : (moves F).Channel → Fin U1) (x : Fin 1) :
    Decidable ((plan F U0 U1).Good n o x) :=
  inferInstanceAs (Decidable True)

/-- The plan obeys the rules, with at most `U0` units for a move. -/
theorem plan_ok : (plan F U0 U1).Ok U0 where
  given_congr _ _ _ _ _ := rfl
  count_congr _ _ _ _ _ := rfl
  good_congr _ _ _ _ _ := Iff.rfl
  given_subset n o z id hid := by
    obtain ⟨k, hk, rfl⟩ := mem_image.1 hid
    exact Plan.mem_cur.2 ⟨Plan.init_mem_seenAt.2 (mem_filter.1 hk).2, fun z' hz' => by omega⟩
  holder_given n o z id hid := by
    obtain ⟨k, -, rfl⟩ := mem_image.1 hid
    exact ⟨false, fun d' => by cases d' <;> rfl⟩
  given_disjoint _ _ _ _ _ h := absurd rfl h
  card_given_le _ _ _ := card_image_le.trans ((card_filter_le _ _).trans (card_fin U0).le)
  count_le _ _ _ := le_rfl

/-- After the move, the current units are the initial units that were not given and the new
units of the channel. -/
example (n : Fin 2 → Fin 2 → Fin (U0 + 1)) (o : (moves F).Channel → Fin U1) :
    (plan F U0 U1).cur n o 1 =
      initialUnits n \ (plan F U0 U1).givenAt n o 0 ∪ newUnits (moves F) 0 o := by
  have h := Plan.cur_succ (n := n) (o := o) (plan_ok (F := F) (U0 := U0) (U1 := U1)) 0
  have h0 : (plan F U0 U1).cur n o (0 : Fin 1) = initialUnits n := by
    ext id
    rcases id with ⟨a, b, k⟩ | ⟨ν, k⟩ <;> simp [Plan.mem_cur]
  rwa [h0] at h

/-- The move keeps the value: the value of the position at the beginning is the sum, over the
outcomes of the move, of the values of the positions after it. The equality law has strings of
one bit and no labels, so `U0 + 1` units on the channel are enough. -/
example (hub : 0 < ub) (n : Fin 2 → Fin 2 → Fin (U0 + 1))
    (init : Fin (2 + 0) → (UnitId 2 U0 (moves F).Channel (U0 + 1) → UnitContent ub) → F)
    (hloc : ∀ a y y', (∀ b c k, y (.init b c k) = y' (.init b c k)) → init a y = init a y')
    (hinit : ∀ a y, init a y ≠ 0 → ∀ id ∈ initialUnits n,
      Play.Holds (UnitId.holder (moves F).channelParty) a id → y id ≠ none) :
    Play.value (UnitId.holder (moves F).channelParty) (none : UnitContent ub) (initialUnits n)
        (initialUnits n) (fun y => ∏ a, init a (y a)) =
      ∑ o : (moves F).Channel → Fin (U0 + 1),
        Play.value (UnitId.holder (moves F).channelParty) none (Plan.seenAt n o 1)
          ((plan F U0 (U0 + 1)).cur n o 1) fun y =>
            ∏ a, partyTable (plan F U0 (U0 + 1)) n o (init a) a (y a) :=
  (Plan.value_moves plan_ok hub (fun _ _ _ _ => trivial) (m := fun _ => 1)
    (fun _ _ _ => le_rfl) (fun _ => by change U0 * (1 + 0) + 1 ≤ U0 + 1; omega) n init hloc
    hinit).trans (sum_congr rfl fun _ _ => ite_eq_left fun _ => trivial)

/-- The identity of the move when no unit is given and the move uses no units: the sum, over the
outcomes and over the common contents of the new units, of the product of the tables of the two
roles is `1`. -/
example (hub : 0 < ub) (hU1 : 0 < U1) (o : (moves F).Channel → Fin U1)
    (y : Fin (2 + 0) → UnitId 2 U0 (moves F).Channel U1 → UnitContent ub)
    (hnew : ∀ ν k a, y a (.new ⟨0, ν⟩ k) = none) :
    ∑ oo : Unit → Fin U1,
      ∑ z ∈ Play.common none (newUnits (moves F) 0 ((moves F).setOutcome o 0 oo)),
      ∏ p, roleTable (moves F) 0 p 0 (fun _ => []) ((moves F).setOutcome o 0 oo)
        (Play.extend (UnitId.holder (moves F).channelParty)
          (newUnits (moves F) 0 ((moves F).setOutcome o 0 oo)) y z ((moves F).party 0 p)) =
      (1 : F) :=
  (move_identity 0 o (fun _ => []) hub (m := 1) (fun _ _ => le_rfl)
    (by change 0 * (1 + 0) + 1 ≤ U1; omega) hnew (by simp) (by simp) (by simp)).trans
    (ite_eq_left (by simp))

end CslibFrontierTests.SeparationMoves
