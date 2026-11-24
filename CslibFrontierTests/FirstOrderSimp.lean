/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

import CslibFrontier.Tactic.FirstOrder.Simp

/-!
# Ordinary-import regression tests for `fo_simp` and `fo_realize`

Exercises `CslibFrontier.Tactic.FirstOrder.Simp` across an ordinary `import` boundary:
* `Formula.Realize` and `Sentence.Realize` bridges (`formula_realize_all`, `formula_realize_ex`,
  `formula_realize_subst`, `sentence_realize_all`);
* `reduceFinSnoc` numeral indexing on nested de Bruijn variables `&0`, `&1`, `&2`, while leaving
  symbolic indices untouched;
* `Matrix.cons_val` at index `2`, `Sum.elim_comp_inl` / `Sum.elim_comp_inr` for one-step
  `Sum.inl` / `Sum.inr` relabelings, and `Function.comp_def` normalizing nested compositions
  produced by `relabel`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.FirstOrderSimp

open FirstOrder Language Structure

private def pairDistinctFormula {L : Language} (α : Type*) : L.Formula α :=
  ∃' ∀' ∼((&0 : L.Term (α ⊕ Fin 2)) =' &1)

private def unaryAllFormula {L : Language} {α : Type*} (R : L.Relations 1) : L.Formula α :=
  ∀' R.boundedFormula₁ (&0 : L.Term (α ⊕ Fin 1))

private def transitiveEqSentence (L : Language) : L.Sentence :=
  ∀' ∀' ∀' (((&0 : L.Term (Empty ⊕ Fin 3)) =' &1 ⊓ (&1 =' &2)) ⟹ (&0 =' &2))

private def substRelFormula {L : Language} {α : Type*} (R : L.Relations 3)
    (x y z : L.Term α) : L.Formula α :=
  (R.formula ![.var (0 : Fin 3), .var 1, .var 2]).subst ![x, y, z]

private noncomputable def relabeledExFormula {L : Language} {α : Type*}
    (R : L.Relations 2) (a : α) : L.Formula α :=
  Formula.iAlls Unit (Formula.iExs Unit
    (R.formula₂ ((Term.var a).relabel (Sum.inl ∘ Sum.inl)) (.var (.inr ()))))

section

variable {L : Language} {M : Type*} [L.Structure M]

-- `formula_realize_ex`, `BoundedFormula.realize_all`, and `reduceFinSnoc` on `&0`, `&1`.
example {α : Type*} (v : α → M) :
    (pairDistinctFormula (L := L) α).Realize v ↔ ∃ x : M, ∀ y : M, x ≠ y := by
  fo_simp [pairDistinctFormula]

-- `sentence_realize_all`, nested `∀'` of depth 3, and `reduceFinSnoc` on `&0`, `&1`, `&2`.
example : M ⊨ transitiveEqSentence L ↔ ∀ a b c : M, a = b ∧ b = c → a = c := by
  fo_simp [transitiveEqSentence]

-- `formula_realize_all` and `reduceFinSnoc` at depth 1 (`n = 0`).
example {α : Type*} (R : L.Relations 1) (v : α → M) :
    (unaryAllFormula R).Realize v ↔ ∀ a : M, RelMap R ![a] := by
  fo_simp [unaryAllFormula]

-- `formula_realize_subst` and `Matrix.cons_val` at index 2.
example {α : Type*} (R : L.Relations 3) (a b c : α) (v : α → M) :
    (substRelFormula R (.var a) (.var b) (.var c)).Realize v ↔
      RelMap R (fun i => ![v a, v b, v c] i) := by
  fo_simp [substRelFormula]
  exact iff_of_eq (congrArg (RelMap R) (funext fun i => by cases i using Fin.cases with
    | zero => rfl
    | succ j => cases j using Fin.cases with
      | zero => rfl
      | succ k => cases k using Fin.cases with | zero => rfl | succ l => exact l.elim0))

-- `Function.comp_def` collapsing nested `Sum.inl ∘ Sum.inl` relabelings.
example {α : Type*} (R : L.Relations 2) (a : α) (v : α → M) :
    (relabeledExFormula R a).Realize v ↔ ∀ _ : Unit → M, ∃ y : Unit → M, RelMap R ![v a, y ()] := by
  fo_simp [relabeledExFormula]

-- `Sum.elim_comp_inl` avoids eta-expanded `fun x => v x` so `omega` equates `t.realize v` atoms.
example {α : Type*} (t : L.Term α) (v : α → ℕ) [L.Structure ℕ] :
    (Formula.iExs Unit ((t.relabel Sum.inl).equal (.var (.inr ())))).Realize v ↔
      ∃ u : Unit → ℕ, t.realize v + 1 = u () + 1 := by
  fo_simp
  exact exists_congr fun _ => by omega

-- Symbolic `Fin.snoc` indices are left untouched by `reduceFinSnoc`.
example (p : Fin 2 → M) (x : M) (i : Fin 3) (h : (Fin.snoc p x : Fin 3 → M) i = x) :
    (Fin.snoc p x : Fin 3 → M) i = x := by
  fail_if_success fo_simp
  exact h

end

end CslibFrontierTests.FirstOrderSimp
