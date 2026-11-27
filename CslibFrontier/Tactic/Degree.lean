/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.Option
public import CslibFrontier.Tactic.FailureNote
public import CslibFrontier.Tactic.OptionMatch
public meta import Lean.Elab.Tactic

/-!
# Degree certificates by composition

`degree` proves a goal `ComputableInDegree f encIn encOut d e` from the `fun_prop` rules of the
operations in `f`. `degree [f, g]` unfolds the named program definitions or local `let` bindings
first. It rewrites each `match` on an option to `Option.elim`, then runs `fun_prop` without
unfolding primitive encodings (`⟨fun a => …, _⟩ : α ↪ List Bool`), discharging degree inequalities
by reflexivity, assumption, `lia`, or decision on ground numerals.

Without `[f, g]`, it does not unfold definitions: unfold a definition with `degree [f]`, or
register a named certificate for it with `fun_prop`. On another goal it fails at once, and when the
search fails the `fun_prop` error ends with a note saying so.

## Main definitions

* `degree`: prove a degree certificate by composition, optionally unfolding `[f, g]`.

## Main results

* `Turing.MultiTapeTM.ComputableInDegree.const_le`, `.cons_le`, `.listAppend_le`, `.natSucc_le`:
  compositional rules for constants, framed-list `::` and `++`, and binary `+ 1`.
* `Turing.MultiTapeTM.ComputableInDegree.boolNot_le`, `.cond_le`, `.unaryIsZero_le`:
  compositional rules for Boolean negation, `cond`, and unary zero tests.
-/

public section

namespace Turing.MultiTapeTM

namespace ComputableInDegree

/-- A constant at any requested cost degree `d ≥ 1` and output degree `e`. -/
@[fun_prop]
theorem const_le {α β : Type*} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    (b : β) {d e : ℕ} (hd : 1 ≤ d) (he : 0 ≤ e) :
    ComputableInDegree (fun _ : α => b) encIn encOut d e :=
  (const b).mono hd he

/-- Prepending an element to a framed list while retaining independent degrees. -/
@[fun_prop]
theorem cons_le {α β : Type} {encIn : α ↪ List Bool} {enc : β ↪ List Bool}
    {f : α → β} {g : α → List β} {df ef dg eg d e : ℕ}
    (hf : ComputableInDegree f encIn enc df ef)
    (hg : ComputableInDegree g encIn (encList enc) dg eg)
    (hd : max (max df dg) (max ef eg) ≤ d) (he : max ef eg ≤ e) :
    ComputableInDegree (fun x => f x :: g x) encIn (encList enc) d e :=
  ((cons enc).comp (hf.prod hg)).mono (by simp only [Nat.mul_one]; omega)
    (by simp only [Nat.mul_one]; omega)

/-- Concatenating two framed lists while retaining independent degrees. -/
@[fun_prop]
theorem listAppend_le {α : Type*} {β : Type} {encIn : α ↪ List Bool} {enc : β ↪ List Bool}
    {f g : α → List β} {df ef dg eg d e : ℕ}
    (hf : ComputableInDegree f encIn (encList enc) df ef)
    (hg : ComputableInDegree g encIn (encList enc) dg eg)
    (hd : max df dg ≤ d) (he : max ef eg ≤ e) :
    ComputableInDegree (fun x => f x ++ g x) encIn (encList enc) d e :=
  (hf.append hg fun _ => by simp).mono hd he

/-- Binary successor of a computed natural number at requested degrees. -/
@[fun_prop]
theorem natSucc_le {α : Type*} {encIn : α ↪ List Bool} {f : α → ℕ} {df ef d e : ℕ}
    (hf : ComputableInDegree f encIn encNat df ef)
    (hd : max df ef ≤ d) (he : ef ≤ e) :
    ComputableInDegree (fun x => f x + 1) encIn encNat d e :=
  (natSucc.comp hf).mono (by simp only [Nat.mul_one]; omega)
    (by simp only [Nat.mul_one]; omega)

/-- Boolean negation of a computed Boolean at requested degrees. -/
@[fun_prop]
theorem boolNot_le {α : Type*} {encIn : α ↪ List Bool} {f : α → Bool} {df ef d e : ℕ}
    (hf : ComputableInDegree f encIn encBool df ef)
    (hd : max df ef ≤ d) (he : 0 ≤ e) :
    ComputableInDegree (fun x => !(f x)) encIn encBool d e :=
  ((of_finite (encIn := encBool) (encMid := encBool) Bool.not).comp hf).mono
    (by simp only [Nat.mul_one]; omega) (by simp only [Nat.mul_zero]; exact he)

/-- Boolean `cond` branching at requested degrees, retaining each branch's output degree. -/
@[fun_prop]
theorem cond_le {α β : Type*} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    {condition : α → Bool} {f g : α → β} {dc ec df ef dg eg d e : ℕ}
    (hc : ComputableInDegree condition encIn encBool dc ec)
    (hf : ComputableInDegree f encIn encOut df ef)
    (hg : ComputableInDegree g encIn encOut dg eg)
    (hd : max dc (max df dg) ≤ d) (he : max ef eg ≤ e) :
    ComputableInDegree (fun x => cond (condition x) (f x) (g x)) encIn encOut d e := by
  simpa only [Bool.cond_eq_ite] using ite_le hc hf hg hd he

/-- Unary zero test on a computed natural number; added as a fallback so `Decidable.decide` is not
tried on every decidable condition during the primary search. -/
theorem unaryIsZero_le {α : Type*} {encIn : α ↪ List Bool} {f : α → ℕ} {df ef d e : ℕ}
    (hf : ComputableInDegree f encIn encUnary df ef)
    (hd : max df ef ≤ d) (he : 0 ≤ e) :
    ComputableInDegree (fun x => decide (f x = 0)) encIn encBool d e := by
  have hz : ComputableInDegree (fun n => decide (n = 0)) encUnary encBool 1 0 :=
    ⟨unary_isZero.1, (DegreeBounded.const 1).mono fun n => by simp [encBool_apply]⟩
  exact (hz.comp hf).mono (by simp only [Nat.mul_one]; omega)
    (by simp only [Nat.mul_zero]; exact he)

end ComputableInDegree

open Lean Meta Elab Tactic in
/-- Whether `e`, under binders, `let`s and metadata, is an embedding `⟨_, _⟩ : α ↪ List Bool`. -/
private meta partial def isEncodingBody (e : Expr) : Bool :=
  match e.consumeMData with
  | .lam _ _ b _ | .letE _ _ _ b _ => isEncodingBody b
  | e => e.isAppOfArity ``Function.Embedding.mk 4 &&
      (e.getArg! 1).isAppOfArity ``List 1 && (e.getArg! 1).appArg!.isConstOf ``Bool

open Lean Meta in
/-- The unfolding predicate of `degree`: the usual one, except that primitive encodings stay folded
during search. -/
private meta def degreeCanUnfold (cfg : Meta.Config) (info : ConstantInfo) : CoreM Bool := do
  if let .defnInfo d := info then
    if isEncodingBody d.value then return false
  match cfg.canUnfoldPredicateConfig with
  | .default => Meta.canUnfoldDefault cfg info
  | .atMatcher => Meta.canUnfoldAtMatcher cfg info

/-- The side-condition discharger of `degree`, proved with the usual unfolding. Internal to
`degree`. -/
syntax (name := degreeDischarge) "degree_discharge" : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| degree_discharge) =>
    withTheReader Meta.Context (fun ctx => { ctx with customCanUnfoldPredicate? := none }) do
      evalTactic (← `(tactic| first | apply le_refl | assumption | lia | decide))

/-- Fallback rules with head `Decidable.decide`, tried only when the primary search fails. -/
private meta def degreeFallbacks : Array Lean.Name := #[
  ``ComputableInDegree.unaryIsZero_le]

/-- Prove `ComputableInDegree f encIn encOut d e` by composing the `fun_prop` rules of the
operations in `f`, optionally unfolding `[f, g]` and rewriting option matches to `Option.elim`. -/
syntax (name := degreeTac) "degree" (" [" ident,* "]")? : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| degree $[[$defs,*]]?) => withMainContext do
    let target := (← instantiateMVars (← getMainTarget)).consumeMData
    unless target.isAppOf ``ComputableInDegree do
      throwError "degree expects a goal `ComputableInDegree f encIn encOut d e`, \
        got{indentExpr target}"
    let defs : Array (TSyntax `ident) := (defs.map (·.getElems)).getD #[]
    let mut globalDefs : Array (TSyntax `ident) := #[]
    for id in defs do
      if (← getLCtx).findFromUserName? id.getId |>.isNone then
        discard <| realizeGlobalConstNoOverloadWithInfo id
        globalDefs := globalDefs.push id
    Cslib.Tactic.withFailureNote m!"degree composes `@[fun_prop]` rules for `ComputableInDegree` \
        and does not unfold definitions. Unfold a local definition first, or prove a certificate \
        for the operation named above and tag it `@[fun_prop]`." do
      for id in defs do
        evalTactic (← `(tactic| try unfold $id:ident))
      if !defs.isEmpty then
        let simpArgs ← defs.mapM fun id => `(Parser.Tactic.simpLemma| $id:ident)
        evalTactic (← `(tactic| try dsimp only [$simpArgs,*]))
      evalTactic (← `(tactic| try option_match_to_elim))
      withCanUnfoldPred degreeCanUnfold do
        let funProp ← `(tactic| fun_prop (config := { maxSteps := 256 })
          (disch := degree_discharge) [$globalDefs,*])
        let s ← saveState
        try
          evalTactic funProp
        catch ex =>
          if degreeFallbacks.isEmpty then throw ex
          s.restore
          try
            for n in degreeFallbacks do
              evalTactic (← `(tactic| have := @$(mkCIdent n)))
            evalTactic funProp
          catch _ =>
            s.restore
            throw ex

end Turing.MultiTapeTM
