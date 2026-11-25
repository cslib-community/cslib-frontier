/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.SelectorNetwork.Numbering

/-!
# Sparse natural addresses for implementation wires

A source-cell number and a bounded local slot give a natural address. Slots zero and one are
reserved for shared edges; private wires use their creation number plus two. An explicit edge
list later compacts the addresses by first-index lookup.

## Main definitions

* `SelectorNetwork.AndOr.Sparse.code`: sparse natural addresses.

## Main results

* `SelectorNetwork.AndOr.Sparse.code_injective`: distinct implementation wires retain distinct
  natural addresses.
-/

public section

attribute [local implicit_reducible] Cslib.Complexity.NCL.Diagram.Inner

namespace Cslib.Complexity.NCL.SelectorNetwork.AndOr.Sparse

variable {U C R : Type*} [DecidableEq U] [DecidableEq C]
variable (N : SelectorNetwork U C R) (A : RowSection N)
variable {m : ℕ} (order : Vert U C R ≃ Fin m) (budget : ℕ)

/-- Shared slots are zero or one; private slots are shifted creation numbers. -/
@[expose] def slot : Edge C R ⊕ Private N A → ℕ
  | .inl (.inl _) => 0
  | .inl (.inr e) => if e.2 then 1 else 0
  | .inr e => 2 + (cell N A e.1).diagram.num e.2.val

/-- The owner-cell number followed by its local slot. -/
@[expose] def code (e : Edge C R ⊕ Private N A) : ℕ :=
  budget * (order (Numbering.edgeOwner N A e)).val + slot N A e

/-- Each shared or private slot lies below the supplied local wire budget. -/
theorem slot_lt
    (hbudget : ∀ v, (cell N A v).top.length + (cell N A v).diagram.innerCount + 2 ≤ budget)
    (e : Edge C R ⊕ Private N A) : slot N A e < budget := by
  have hb := hbudget (Numbering.edgeOwner N A e)
  rcases e with (c | ⟨r, b⟩) | ⟨v, e⟩
  · change 0 < budget
    omega
  · change (if b then 1 else 0) < budget
    cases b <;> simp <;> omega
  · have := (cell N A v).diagram.num_lt e.val
    change 2 + (cell N A v).diagram.num e.val < budget
    change (cell N A v).top.length + (cell N A v).diagram.innerCount + 2 ≤ budget at hb
    omega

private theorem owner_eq_of_code_eq
    (hbudget : ∀ v, (cell N A v).top.length + (cell N A v).diagram.innerCount + 2 ≤ budget)
    {e f : Edge C R ⊕ Private N A} (h : code N A order budget e = code N A order budget f) :
    Numbering.edgeOwner N A e = Numbering.edgeOwner N A f := by
  have he := slot_lt N A budget hbudget e
  have hf := slot_lt N A budget hbudget f
  apply order.injective
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hm := Nat.mul_le_mul_left budget (Nat.succ_le_of_lt hlt)
    simp only [Nat.mul_succ] at hm
    unfold code at h
    omega
  · have hm := Nat.mul_le_mul_left budget (Nat.succ_le_of_lt hgt)
    simp only [Nat.mul_succ] at hm
    unfold code at h
    omega

private theorem eq_of_owner_slot_eq {e f : Edge C R ⊕ Private N A}
    (howner : Numbering.edgeOwner N A e = Numbering.edgeOwner N A f)
    (hslot : slot N A e = slot N A f) : e = f := by
  rcases e with (c | ⟨r, b⟩) | ⟨v, e⟩ <;> rcases f with (d | ⟨r', b'⟩) | ⟨v', f⟩ <;>
    dsimp only [slot, Numbering.edgeOwner] at howner hslot
  · exact congrArg (Sum.inl ∘ Sum.inl) (Sum.inl.inj (Sum.inr.inj howner))
  · cases howner
  · change 0 = 2 + _ at hslot
    omega
  · cases howner
  · obtain rfl : r = r' := Sum.inr.inj (Sum.inr.inj howner)
    cases b <;> cases b' <;> simp_all
  · change (if b then 1 else 0) = 2 + _ at hslot
    cases b <;> simp only [ite_true, ite_false, Bool.false_eq_true] at hslot <;> omega
  · change 2 + _ = 0 at hslot
    omega
  · change 2 + _ = if b' then 1 else 0 at hslot
    cases b' <;> simp only [ite_true, ite_false, Bool.false_eq_true] at hslot <;> omega
  · obtain rfl : v = v' := howner
    exact congrArg (fun e => Sum.inr (⟨v, e⟩ : Private N A)) <| Subtype.ext <|
      (cell N A v).diagram.num_injective (Nat.add_left_cancel (hslot : 2 + _ = 2 + _))

/-- Bounded slots in distinct source cells give distinct natural wire names. -/
theorem code_injective
    (hbudget : ∀ v, (cell N A v).top.length + (cell N A v).diagram.innerCount + 2 ≤ budget) :
    Function.Injective (code N A order budget) := by
  intro e f h
  have ho := owner_eq_of_code_eq N A order budget hbudget h
  apply eq_of_owner_slot_eq N A ho
  simpa only [code, ho, Nat.add_left_cancel_iff] using h

end Cslib.Complexity.NCL.SelectorNetwork.AndOr.Sparse
