/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public meta import Lean.Meta.DiscrTree

/-!
# The attribute `growth_poly`

Declares the attribute `growth_poly` and the discrimination-tree tables it populates, in a file of
its own so `ResourceBounds.Polynomial.Automation` and downstream modules can tag rules with
`@[growth_poly]`.

`@[growth_poly]` accepts two theorem shapes:

* **Pointwise bounds and equations in `ℕ`:** `∀ …, lhs ≤ rhs` or `∀ …, lhs = rhs`, indexed by
  `lhs`. When `growth_poly` encounters a term matching `lhs`, it bounds it via `PolyBounded.mono`
  by `rhs` and continues recursively.
* **Closure rules for `PolyBounded`:** `∀ …, PolyBounded size (fun a => op …)`, indexed by `op …`.
  When `growth_poly` encounters a term matching `op …`, it applies the rule and proves the
  remaining `PolyBounded` subgoals recursively.

A tag on a private theorem is visible only in its own module.

## Main definitions

* `growth_poly`: attribute registering a pointwise `ℕ` bound/equation or a `PolyBounded` closure
  rule for the `growth_poly` tactic.
* `Cslib.Tactic.GrowthPoly.boundSides?`: extracts `(lhs, rhs, isEq)` from `lhs ≤ rhs` or
  `lhs = rhs` in `ℕ`.
* `Cslib.Tactic.GrowthPoly.boundExt`: discrimination tree of registered `ℕ` bound/equation rules.
* `Cslib.Tactic.GrowthPoly.closureExt`: discrimination tree of registered `PolyBounded` closure
  rules.
-/

public meta section

namespace Cslib.Tactic.GrowthPoly

open Lean Meta

/-- The sides of a bound `lhs ≤ rhs` or an equation `lhs = rhs` between natural numbers, together
with whether it is an equation. -/
def boundSides? (e : Expr) : Option (Expr × Expr × Bool) :=
  match_expr e.consumeMData with
  | LE.le α _ lhs rhs => if α.isConstOf ``Nat then some (lhs, rhs, false) else none
  | Eq α lhs rhs => if α.isConstOf ``Nat then some (lhs, rhs, true) else none
  | _ => none

initialize registerTraceClass `growth_poly

/-- Registered pointwise `ℕ` bound/equation rules (`lhs ≤ rhs` or `lhs = rhs`), indexed by `lhs`. -/
initialize boundExt : SimpleScopedEnvExtension (Array DiscrTree.Key × Name) (DiscrTree Name) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun tree (keys, decl) => tree.insertKeyValue keys decl
    initial := {}
    exportEntry? := fun _ entry =>
      if isPrivateName entry.2 then ⟨none, none, some entry⟩ else .uniform (some entry)
  }

/-- Registered `PolyBounded` closure rules, indexed by the body of the bounded function. -/
initialize closureExt : SimpleScopedEnvExtension (Array DiscrTree.Key × Name) (DiscrTree Name) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun tree (keys, decl) => tree.insertKeyValue keys decl
    initial := {}
    exportEntry? := fun _ entry =>
      if isPrivateName entry.2 then ⟨none, none, some entry⟩ else .uniform (some entry)
  }

/-- `@[growth_poly]` registers a theorem for the `growth_poly` tactic. Supported conclusions are:

* `lhs ≤ rhs` or `lhs = rhs` in `ℕ`, where `lhs` has a non-variable head (for example
  `Nat.log2_le_self` or `(l.filter p).length ≤ l.length`);
* `Turing.MultiTapeTM.PolyBounded size (fun a => op …)`, where `op …` has a non-variable head.

A tag on a private theorem is used in its own module only. -/
syntax (name := growthPolyAttr) "growth_poly" : attr

initialize registerBuiltinAttribute {
  name := `growthPolyAttr
  descr := "a pointwise `ℕ` bound/equation or `PolyBounded` closure rule for `growth_poly`"
  applicationTime := .afterTypeChecking
  add := fun decl _ kind => do
    let entry ← MetaM.run' do
      let (_, _, concl) ← forallMetaTelescope (← getConstInfo decl).type
      let concl ← whnfR concl
      if let some (lhs, _, _) := boundSides? concl then
        if lhs.getAppFn.isMVar then
          throwError "`growth_poly` requires a non-variable head on the left-hand side, \
            got{indentExpr lhs}"
        return Sum.inl (← DiscrTree.mkPath lhs)
      if concl.isAppOfArity `Turing.MultiTapeTM.PolyBounded 3 then
        let u := concl.getArg! 2
        let .forallE _ α _ _ ← whnfR (← inferType u) |
          throwError "`growth_poly`: expected a function in `PolyBounded`, got{indentExpr u}"
        let x ← mkFreshExprMVar α
        let body := (u.beta #[x]).headBeta
        if body.getAppFn.isMVar then
          throwError "`growth_poly` requires a non-variable head in `PolyBounded`, \
            got{indentExpr body}"
        return Sum.inr (← DiscrTree.mkPath body)
      throwError "`growth_poly` expects a theorem concluding `lhs ≤ rhs`, `lhs = rhs` in `ℕ`, or \
        `Turing.MultiTapeTM.PolyBounded size (fun a => op …)`, got{indentExpr concl}"
    match entry with
    | .inl keys => boundExt.add (keys, decl) kind
    | .inr keys => closureExt.add (keys, decl) kind
}

end Cslib.Tactic.GrowthPoly

end
