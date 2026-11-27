/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Operator.Polarity
import CslibFrontier.Tactic.FirstOrder.Simp

/-!
# Blocks of quantifiers in operator formulas

`Formula.exs` binds a finite tuple of fresh first-order variables. Its semantics, formation
check, and polarity check reduce to those of its body. This supplies the quantifier blocks
needed when pulling fixed-point formulas back along tuple interpretations.
-/

public section

universe u v w z s

open FirstOrder Language

namespace Cslib.Logic.FO.Operator.Formula

variable {L : Language.{u, v}} {O : Type s} {shape : O → Shape}
  {Γ : List ℕ} {α : Type w}

/-- Bind all variables in the right summand, in increasing coordinate order. -/
@[expose] def exs : {α : Type w} → (n : ℕ) →
    Formula L shape Γ (α ⊕ Fin n) → Formula L shape Γ α
  | _, 0, φ => φ.relabel (Sum.elim id Fin.elim0)
  | _, n + 1, φ => .ex (exs n (φ.relabel (Sum.elim
      (fun a => Sum.inl (some a))
      (Fin.cases (Sum.inl none) Sum.inr))))

/-- A block of existential quantifiers chooses one complete tuple. -/
@[simp, fo_realize] theorem realize_exs {M : Type z} [L.Structure M]
    (I : Interpretation shape M) (n : ℕ) (φ : Formula L shape Γ (α ⊕ Fin n))
    (ρ : RelEnv Γ M) (v : α → M) :
    (φ.exs n).Realize I ρ v ↔ ∃ xs, φ.Realize I ρ (Sum.elim v xs) := by
  induction n generalizing α with
  | zero =>
    simp only [exs, realize_relabel]
    have h (xs : Fin 0 → M) : v ∘ Sum.elim id Fin.elim0 = Sum.elim v xs :=
      funext fun | .inl _ => rfl | .inr i => i.elim0
    exact ⟨fun hx => ⟨Fin.elim0, h _ ▸ hx⟩, fun ⟨xs, hx⟩ => h xs ▸ hx⟩
  | succ n ih =>
    fo_simp [exs, ih]
    have h (x : M) (xs : Fin n → M) :
        (fun y => Sum.elim (fun o => o.elim x v) xs
          (Sum.elim (fun a => Sum.inl (some a)) (Fin.cases (Sum.inl none) Sum.inr) y)) =
          Sum.elim v (Fin.cons x xs) :=
      funext fun | .inl _ => rfl | .inr i => Fin.cases rfl (fun _ => rfl) i
    refine ⟨fun ⟨x, xs, hx⟩ => ⟨Fin.cons x xs, h x xs ▸ hx⟩, fun ⟨xs, hx⟩ => ?_⟩
    refine ⟨xs 0, Fin.tail xs, ?_⟩
    rw [h, Fin.cons_self_tail]
    exact hx

/-- Quantifying a tuple leaves the formation check unchanged. -/
@[simp] theorem wellFormed_exs (policy : Policy shape) (n : ℕ)
    (φ : Formula L shape Γ (α ⊕ Fin n)) :
    (φ.exs n).wellFormed policy = φ.wellFormed policy := by
  induction n generalizing α with
  | zero => simp [exs]
  | succ n ih => simp only [exs, wellFormed, ih, wellFormed_relabel]

/-- Quantifying a tuple leaves dependence on scoped relations unchanged. -/
@[simp] theorem checkPolarity_exs (variance : Variances shape) (n : ℕ)
    (φ : Formula L shape Γ (α ⊕ Fin n)) (sign : Bool) (mark : Marking Γ) :
    (φ.exs n).checkPolarity variance sign mark = φ.checkPolarity variance sign mark := by
  induction n generalizing α with
  | zero => simp [exs]
  | succ n ih => simp only [exs, checkPolarity, ih, checkPolarity_relabel]

end Cslib.Logic.FO.Operator.Formula
