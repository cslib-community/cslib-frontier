/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.PlayMoves
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.GroupProgram.Accept
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.GroupProgram.Theorem
import Mathlib.Data.Fintype.BigOperators

/-! Tests of the script of a group and of the program GROUP, as a client that sees only the
public statements.

* The indices below a number, and the flags of the partners in a row.
* For a plan of two parties with one move with the equality law (the fixtures of
  `CslibFrontierTests.SeparationMoves`) and the group of both parties, the instruction of every
  role is in the script of the group, and all instructions of the script are valid when the two
  roles of the equality law are listed.
* `exists_group` for this plan: the plain sum of GROUP at the script of the group is the value of
  the group. -/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.SeparationGroupTheorem

open Cslib Cslib.Circuits.Arithmetic.Separation Cslib.Circuits.Arithmetic.Separation.Cut
  Cslib.Circuits.Arithmetic.Separation.Interpreter
  Cslib.Circuits.Arithmetic.Separation.GroupProgram Finset

/-! ### Closed examples -/

/-- The indices below `2`. -/
example : indicesBelow (2 : Fin 4) = [0, 1] := by decide

/-- A party that writes for the partners `1` to `3`: the flags of the partners `0`, `1`, `2`
and `3` are `0`, `1`, `2` and `1`. -/
example : List.ofFn (rowFlag (A := 4) ⟨false, 1, 3⟩) = [0, 1, 2, 1] := by decide

/-! ### The script of a group for one move -/

variable {F : Type} [CommRing F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S]
  [DecidableEq S] [Fintype Q] [DecidableEq Q] {c U0 U1 : ℕ}

/-- The equality law: the roles are `false` and `true`, with one slot and one channel between
them. There is one index, and the string on the channel is one bit. The table of a role is `1`
when its copy of the bit of the slot is the bit on the channel. -/
private def equalityLaw (F : Type) [CommSemiring F] : Law F where
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
private def moves (F : Type) [CommSemiring F] : Moves F (1 + 1 + 0) 1 where
  law _ := equalityLaw F
  party _ (d : Bool) := if d then 1 else 0
  party_injective _ := by
    rintro (_ | _) (_ | _) h <;> first | rfl | simp at h

/-- The plan that gives all units of the string from the party `0` to the party `1` at the slot
of the move. The move uses `U0` units, and all outcomes are allowed. -/
private def plan (F : Type) [CommSemiring F] (U0 U1 : ℕ) : Plan (moves F) U0 U1 where
  given n _ _ := (univ.filter fun k : Fin U0 => (k : ℕ) < n 0 1).image (UnitId.init 0 1)
  count _ _ _ := U0
  Good _ _ _ := True

instance (n : Fin 2 → Fin 2 → Fin (U0 + 1)) (o : (moves F).Channel → Fin U1) (x : Fin 1) :
    Decidable ((plan F U0 U1).Good n o x) :=
  inferInstanceAs (Decidable True)

/-- The plan obeys the rules, with at most `U0` units for a move. -/
private theorem plan_ok : (plan F U0 U1).Ok U0 where
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

/-- The two roles of the equality law. -/
private def kinds (F : Type) [CommRing F] : List (Σ L : Law F, L.Role) :=
  [⟨equalityLaw F, false⟩, ⟨equalityLaw F, true⟩]

/-- The number of a role in `kinds`. -/
private def tag (r : (moves F).Role) : ℕ := (show Bool from r.2).toNat

private theorem kinds_tag (r : (moves F).Role) :
    (kinds F)[tag r]? = some ⟨(moves F).law r.1, r.2⟩ := by
  obtain ⟨x, d⟩ := r
  obtain rfl : x = 0 := Subsingleton.elim _ _
  change Bool at d
  cases d <;> rfl

variable (qn : Q → ℕ) (cb : Option Γ → Fin c → Bool) (q : Fin 2 → Q) (x : Fin 1 → List Γ)
  (ρ : Option S → Fin 2 → RowData 2) (n : Fin 2 → Fin 2 → Fin 1)
  (o : (moves F).Channel → Fin 1) (key : Cell (moves F) 0 1 → List Bool)
  (dkey : Fin 2 × Fin 0 → List Bool) {ub : ℕ} (b : UnitId 2 0 (moves F).Channel 1 → UnitContent ub)

/-- In the group of both parties, the instruction of every role is in the script. -/
example (r : (moves F).Role) :
    roleInstruction (plan F 0 1) n o key tag r ∈
      groupScript qn cb (plan F 0 1) q x ρ n o (fun _ => ()) () key dkey tag b := by
  simp [groupScript, mem_groupRoles]

/-- All instructions of the script are valid for GROUP. -/
example : ∀ i ∈ groupScript (fun z => (Fintype.equivFin Q z : ℕ)) cb (plan F 0 1) q x ρ n o
    (fun _ => ()) () key dkey tag b, i.Valid Q c (kinds F) :=
  valid_groupScript cb (kinds F) kinds_tag b

/-- **GROUP for one move.** If the automaton and the tables of the equality law are values of
formulas, one formula is GROUP for the plan: at the script of the group of both parties, its plain
sum is the value of the group. -/
example {θ : List Bool → F} (mu : Tape.Letter S Unit Γ → Matrix Q Q F)
    (hmu : ∀ z q q', ∃ e : WE, e.val θ = mu z q q')
    (htab : ∀ z ∈ kinds F, ∀ i v g', ∃ e : WE, e.val θ = z.1.table z.2 i v g') :
    ∃ GROUP : Fm, ∀ (bT bub : List Bool)
      (b : UnitId 2 0 (moves F).Channel 1 → UnitContent (BitString.binaryValue bub)),
      Function.Injective (Sum.elim key dkey) → 0 < BitString.binaryValue bub →
      (∀ κ, (x κ).length ≤ BitString.binaryValue bT) →
      (∀ s p, (ρ s p).empty = false → (ρ s p).first ≤ (ρ s p).last) →
      pv θ (.cons GROUP.code (scriptEnc bT bub (groupScript (fun z => (Fintype.equivFin Q z : ℕ))
        cb (plan F 0 1) q x ρ n o (fun _ => ()) () key dkey tag b))) =
        (plan F 0 1).groupValue mu (BitString.binaryValue bT) cb q x ρ n o (fun _ => ()) () b := by
  obtain ⟨GROUP, κ, h⟩ := exists_group mu cb (kinds F) hmu htab
  exact ⟨GROUP, fun bT bub b hκ hub hx hρ =>
    (h (plan F 0 1) q x ρ n o _ () key dkey tag bT bub b hκ hub plan_ok hx hρ kinds_tag).2.1⟩

end CslibFrontierTests.SeparationGroupTheorem
