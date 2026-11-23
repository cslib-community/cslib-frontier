/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Tactic.FirstOrder.Init
public import Mathlib.ModelTheory.Semantics

/-!
# The `fo_simp` tactic

`fo_simp` simplifies with the simp set `fo_realize`, which unfolds the realization of first-order
formulas to propositions about the structure they are evaluated in. This file tags Mathlib's
realization lemmas, and the propositional normalizations they need, with `fo_realize`, and
defines `fo_simp`. Lemmas about the formulas, projection formulas and interpreted structures of
this library are tagged where they are proved.

It depends only on Mathlib's semantics of first-order logic, so that the modules of
`CslibFrontier.Logics` below `CslibFrontier.Tactic.FirstOrder` can import it to prove realization
lemmas. `CslibFrontier.Tactic.FirstOrder` re-exports it, together with the simprocs that unfold
concrete interpretations and projections.

## Main definitions

* `fo_simp`: `simp only` with the simp set `fo_realize`.
* `Cslib.Tactic.FirstOrder.reduceFinSnoc`: `fo_realize` `dsimproc` evaluating `Fin.snoc` at concrete
  numeral indices.
* `Cslib.Tactic.FirstOrder.formula_realize_all`, `Cslib.Tactic.FirstOrder.formula_realize_ex`,
  `Cslib.Tactic.FirstOrder.formula_realize_subst`, `Cslib.Tactic.FirstOrder.sentence_realize_all`:
  `Formula.Realize` and `Sentence.Realize` bridge lemmas for quantifiers and term substitution.
-/

public section

open Lean Meta Parser.Tactic

namespace Cslib.Tactic.FirstOrder

section RealizeBridges

open _root_.FirstOrder _root_.FirstOrder.Language

universe u v u' w

variable {L : Language.{u, v}} {M : Type w} [L.Structure M]

/-- Universal quantification on a formula unfolds to universal quantification over a single bound
variable environment `Fin.snoc default a`. -/
@[simp, fo_realize]
theorem formula_realize_all {α : Type u'} (θ : L.BoundedFormula α 1) (v : α → M) :
    Formula.Realize (∀' θ) v ↔ ∀ a : M, θ.Realize v (Fin.snoc default a) :=
  BoundedFormula.realize_all

/-- Existential quantification on a formula unfolds to existential quantification over a single
bound variable environment `Fin.snoc default a`. -/
@[simp, fo_realize]
theorem formula_realize_ex {α : Type u'} (θ : L.BoundedFormula α 1) (v : α → M) :
    Formula.Realize (∃' θ) v ↔ ∃ a : M, θ.Realize v (Fin.snoc default a) :=
  BoundedFormula.realize_ex

/-- Realizing a term-substituted formula evaluates the substituted terms in the environment. -/
@[simp, fo_realize]
theorem formula_realize_subst {α β : Type*} (φ : L.Formula α) (tf : α → L.Term β) (v : β → M) :
    Formula.Realize (φ.subst tf) v ↔ φ.Realize fun a => (tf a).realize v :=
  BoundedFormula.realize_subst

/-- Universal quantification on a sentence unfolds to universal quantification over `M`. -/
@[simp, fo_realize]
theorem sentence_realize_all (θ : L.BoundedFormula Empty 1) :
    M ⊨ (∀' θ : L.Sentence) ↔ ∀ a : M, θ.Realize default (Fin.snoc default a) :=
  BoundedFormula.realize_all

end RealizeBridges

private meta def evalNatLit? (e : Expr) : MetaM (Option Nat) := do
  let e ← withDefault <| whnfD e
  if let some k := e.rawNatLit? then return some k
  if let some k := e.nat? then return some k
  return none

/-- Evaluate `Fin.snoc p x i` at a concrete numeral index `i` over a concrete length `n + 1`, so
that de Bruijn variables `&0`, `&1`, … under nested `∀'` and `∃'` quantifiers reduce without
unfolding `Fin.snoc` generally. -/
dsimproc [fo_realize] reduceFinSnoc (@Fin.snoc _ _ _ _ _) := fun e => do
  unless e.isAppOfArity ``Fin.snoc 5 do return .continue
  let args := e.getAppArgs
  let some n ← evalNatLit? args[0]! | return .continue
  let p := args[2]!
  let x := args[3]!
  unless args[4]!.isAppOfArity ``OfNat.ofNat 3 do return .continue
  let some k ← evalNatLit? (args[4]!.getArg! 1) | return .continue
  let k' := k % (n + 1)
  if k' == n then
    unless ← withDefault <| isDefEq e x do return .continue
    return .visit x
  else
    let finN ← mkAppM ``Fin #[mkNatLit n]
    let idx ← withDefault <| mkNumeral finN k'
    let res := mkApp p idx
    unless ← withDefault <| isDefEq e res do return .continue
    return .visit res

attribute [fo_realize high] Sum.elim_comp_inl Sum.elim_comp_inr

open FirstOrder.Language in
attribute [fo_realize]
  BoundedFormula.realize_bot BoundedFormula.realize_not BoundedFormula.realize_bdEqual
  BoundedFormula.realize_top BoundedFormula.realize_inf BoundedFormula.realize_imp
  BoundedFormula.realize_rel BoundedFormula.realize_rel₁ BoundedFormula.realize_rel₂
  BoundedFormula.realize_sup BoundedFormula.realize_all BoundedFormula.realize_ex
  BoundedFormula.realize_iff BoundedFormula.realize_relabel BoundedFormula.realize_iSup
  BoundedFormula.realize_iInf BoundedFormula.realize_iAlls BoundedFormula.realize_iExs
  Formula.realize_not Formula.realize_bot Formula.realize_top Formula.realize_inf
  Formula.realize_imp Formula.realize_rel Formula.realize_rel₁ Formula.realize_rel₂
  Formula.realize_sup Formula.realize_iff Formula.realize_relabel Formula.realize_equal
  Formula.realize_iSup Formula.realize_iInf Formula.realize_iAlls Formula.realize_iExs
  Sentence.realize_not Sentence.realize_top Sentence.realize_inf Sentence.realize_sup
  Sentence.realize_imp Sentence.realize_iff
  LHom.realize_onBoundedFormula LHom.realize_onFormula LHom.realize_onSentence
  Term.realize_var Term.realize_relabel
  Sum.elim_inl Sum.elim_inr Function.comp_apply Function.comp_def
  Unique.forall_iff PUnit.default_eq_unit
  Matrix.cons_val Matrix.cons_val_zero Matrix.cons_val_one Matrix.head_cons Matrix.cons_val_fin_one
  Set.mem_ofPred_eq
  true_and and_true false_and and_false true_or or_true false_or or_false not_true_eq_false
  not_false_eq_true not_not ne_eq iff_self eq_self_iff_true implies_true true_implies
  false_implies imp_false forall_const Bool.false_eq_true exists_prop
  ite_true ite_false

/-- `fo_simp` simplifies with the simp set `fo_realize`, unfolding the realization of first-order
formulas, projection formulas and the relations of interpreted structures, and, where
`CslibFrontier.Tactic.FirstOrder` is imported, the definitions of concrete interpretations and
projections. `fo_simp (config := c) (disch := tac) [h₁, h₂] at l` passes a configuration,
discharger, extra simp lemmas and a location through, as for `simp only`. -/
syntax (name := foSimp) "fo_simp" optConfig (discharger)? (simpArgs)? (location)? : tactic

macro_rules
  | `(tactic| fo_simp $cfg:optConfig $[$disch]? $[[$args,*]]? $[at $location]?) =>
    let args := args.map (·.getElems) |>.getD #[]
    `(tactic| simp $cfg:optConfig $[$disch]? only [fo_realize, $args,*] $[at $location]?)

end Cslib.Tactic.FirstOrder
