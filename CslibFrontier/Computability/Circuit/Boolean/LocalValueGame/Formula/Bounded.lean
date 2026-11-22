/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.LocalValueGame.Formula
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite

/-!
# Finite local formulas for a succinct Boolean decoder

For fixed input count and depth, local Boolean formulas form a finite type. Their encoding can
therefore be fixed independently of all runtime circuit parameters. Operation lookup and movement
inside a local formula are finite functions; following a source port still requires the actual
native macro-node router.

The stopping-product compiler uses seven inputs and depth twelve. Its finite local control never
contains an assignment word or a value of a tensor entry.
-/

public section

namespace Cslib.Circuits.Boolean.LocalValueGame.FormulaExpansion

/-- A local Boolean formula with a fixed, parameter-independent depth bound. -/
abbrev BoundedFormula (n depth : ℕ) := {f : Formula signature n // f.depth ≤ depth}

private def layer {n d : ℕ} (f : BoundedFormula n (d + 1)) :
    Fin n ⊕ (Σ op : Op, Fin (signature.Arity op) → BoundedFormula n d) :=
  match f with
  | ⟨.input i, _⟩ => .inl i
  | ⟨.gate op args, h⟩ => .inr ⟨op, fun i => ⟨args i, by
      have hi := Finset.le_sup (f := fun j => (args j).depth) (Finset.mem_univ i)
      have hb : (Finset.univ.sup fun j => (args j).depth) + 1 ≤ d + 1 := h
      omega⟩⟩

private theorem layer_injective {n d : ℕ} : Function.Injective (layer (n := n) (d := d)) := by
  rintro ⟨f, hf⟩ ⟨g, hg⟩ h
  apply Subtype.ext
  cases f with
  | input i =>
    cases g with
    | input j => simpa [layer] using h
    | gate op args => simp [layer] at h
  | gate op args =>
    cases g with
    | input j => simp [layer] at h
    | gate op' args' =>
      have he := Sum.inr.inj h
      have hop := congrArg Sigma.fst he
      change op = op' at hop
      subst op'
      have ha := (Sigma.mk.inj_iff.mp he).2
      have heq : (fun i => (⟨args i, _⟩ : BoundedFormula n d)) =
          (fun i => (⟨args' i, _⟩ : BoundedFormula n d)) := eq_of_heq ha
      have hargs : args = args' :=
        funext fun i => congrArg Subtype.val (congrFun heq i)
      cases hargs
      rfl

/-- Bounded local formulas have a finite control representation for each fixed arity and depth. -/
instance (n d : ℕ) : Finite (BoundedFormula n d) := by
  induction d with
  | zero =>
    let f : BoundedFormula n 0 → Fin n := fun x => match x with
      | ⟨.input i, _⟩ => i
      | ⟨.gate _ _, h⟩ => False.elim (by simp [Formula.depth] at h)
    apply Finite.of_injective f
    rintro ⟨a, ha⟩ ⟨b, hb⟩ h
    cases a with
    | input i =>
      cases b with
      | input j => simpa [f] using h
      | gate op args =>
        have : (Finset.univ.sup fun j => (args j).depth) + 1 ≤ 0 := hb
        omega
    | gate op args =>
      have : (Finset.univ.sup fun j => (args j).depth) + 1 ≤ 0 := ha
      omega
  | succ d ih =>
    let := ih
    exact Finite.of_injective layer layer_injective

/-- Unary rank in one fixed finite enumeration; no runtime parameter affects this layout. -/
noncomputable abbrev encBoundedFormula (n d : ℕ) : BoundedFormula n d ↪ List Bool :=
  Turing.MultiTapeTM.encFinite (BoundedFormula n d)

namespace BoundedFormula

variable {n d : ℕ}

/-- The selected local instruction is either a source port or an ordinary Boolean gate. -/
@[expose] def operation (f : BoundedFormula n d) : Fin n ⊕ Op :=
  match f.val with
  | .input i => .inl i
  | .gate op _ => .inr op

private theorem argument_depth_le {op : Op} {args : Fin (signature.Arity op) → Formula signature n}
    (h : (Formula.gate (σ := signature) op args).depth ≤ d)
    (i : Fin (signature.Arity op)) :
    (args i).depth ≤ d := by
  have hi := Finset.le_sup (f := fun j => (args j).depth) (Finset.mem_univ i)
  change (Finset.univ.sup fun j => (args j).depth) + 1 ≤ d at h
  omega

/-- Follow a local gate edge, retaining input and constant leaves until the macro router handles
those terminals. A NOT gate ignores the selected branch. -/
@[expose] def child (f : BoundedFormula n d) (b : Bool) : BoundedFormula n d :=
  match f with
  | ⟨.input i, h⟩ => ⟨.input i, h⟩
  | ⟨.gate (.const v) args, h⟩ => ⟨.gate (.const v) args, h⟩
  | ⟨.gate .not args, h⟩ => ⟨args 0, by exact argument_depth_le h 0⟩
  | ⟨.gate .and args, h⟩ =>
      ⟨args (if b then 1 else 0), by exact argument_depth_le h (if b then 1 else 0)⟩
  | ⟨.gate .or args, h⟩ =>
      ⟨args (if b then 1 else 0), by exact argument_depth_le h (if b then 1 else 0)⟩

/-- Inside a gate, finite local control follows exactly the existing formula decoder. -/
theorem child_val {α : Type} (template : α → Formula signature n)
    (source : α → Fin n → Option α) (a : α) (f : BoundedFormula n d) (b : Bool)
    (hg : ∀ i, f.val ≠ .input i) :
    (decoder template source).child ⟨a, f.val⟩ b = ⟨a, (child f b).val⟩ := by
  rcases f with ⟨f, hf⟩
  cases f with
  | input i => exact (hg i rfl).elim
  | gate op args => cases op <;> rfl

end BoundedFormula

end Cslib.Circuits.Boolean.LocalValueGame.FormulaExpansion
