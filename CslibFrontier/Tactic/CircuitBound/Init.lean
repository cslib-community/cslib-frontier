/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public meta import Lean.Meta.Tactic.Simp.RegisterCommand

/-!
# The attribute `circuit_bound`

Declares the attribute `circuit_bound` and the table of bounds it fills, in a file of its own
because an attribute cannot be used in the file declaring it. The tactic `circuit_bound` of
`CslibFrontier.Tactic.CircuitBound` reads the table.

## Main definitions

* `circuit_bound`: registers a bound `m ≤ b` or a value `m = b` of a natural number `m`, such as
  the depth of a named circuit, for the tactic `circuit_bound`.
* `circuit_simps`: the simp set the tactic normalizes with.

`set_option trace.circuit_bound true` shows the registered bounds and hypotheses the tactic uses.
-/

public meta section

/-- The simp set `circuit_simps` rewrites the function, the size, the program cost and the exact
depths of a circuit built with combinators such as `Circuit.comp`, `Circuit.append`, `Circuit.pi`,
`Circuit.wiring`, `Circuit.oneGate` and `Formula.toCircuit` to those of its parts. It unfolds no
definition: name the construction's own definitions beside it, as in
`simp only [circuit_simps, step]`. `CslibFrontier.Computability.Circuit.Simps` lists its lemmas.

Seven of them are general: `Fin.append_left`, `Fin.append_right`, `Function.comp_apply`,
`Finset.sum_const`, `Finset.card_univ`, `Fintype.card_fin` and `smul_eq_mul` rewrite every matching
subterm of the goal, not only what the circuit lemmas produce. A step that follows
`simp only [circuit_simps, …]` and depends on the shape of the goal, such as `congr` or
`exact (Fin.append_left _ _ i).trans h`, sees the goal after these rewrites. -/
register_simp_attr circuit_simps

namespace Cslib.Tactic.CircuitBound

open Lean Meta

/-- The sides of a bound `lhs ≤ rhs` or a value `lhs = rhs` between natural numbers, and whether it
is an equation. -/
def boundSides? (e : Expr) : Option (Expr × Expr × Bool) :=
  match_expr e.consumeMData with
  | LE.le α _ lhs rhs => if α.isConstOf ``Nat then some (lhs, rhs, false) else none
  | Eq α lhs rhs => if α.isConstOf ``Nat then some (lhs, rhs, true) else none
  | _ => none

initialize registerTraceClass `circuit_bound

/-- The registered bounds, indexed by their left-hand sides. -/
initialize boundExt : SimpleScopedEnvExtension (Array DiscrTree.Key × Name) (DiscrTree Name) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun bounds (keys, decl) => bounds.insertKeyValue keys decl
    initial := {}
    -- as in core's simp extension (`mkSimpExt`), a tag on a private theorem stays in its module
    exportEntry? := fun _ entry =>
      if isPrivateName entry.2 then ⟨none, none, some entry⟩ else .uniform (some entry)
  }

/-- `@[circuit_bound]` registers a theorem `m ≤ b` or `m = b` between natural numbers for the
tactic `circuit_bound`, which uses it to bound `m` wherever `m` occurs in the quantity it bounds.
Typical uses are the depth, size or cost of a named circuit, `(adder w).depth ≤ 6`, and the rule of
a combinator, `(d.comp c).depth ≤ d.depth + c.depth`: the tactic goes on to bound the right-hand
side.

A hypothesis `∀ j, m' j ≤ D` whose bound `D` occurs nowhere on the left-hand side, as in
`(∀ j, (cs j).depth ≤ D) → (Circuit.pi cs).depth ≤ D`, asks the tactic for a bound of `m' j` that
does not depend on `j`. Any other hypothesis must be among the local hypotheses.

A tag on a private theorem is used in its own module only. -/
syntax (name := circuitBoundAttr) "circuit_bound" : attr

initialize registerBuiltinAttribute {
  name := `circuitBoundAttr
  descr := "a bound on a natural number, such as the depth of a circuit, for `circuit_bound`"
  applicationTime := .afterTypeChecking
  add := fun decl _ kind => do
    let keys ← MetaM.run' do
      let (_, _, conclusion) ← forallMetaTelescope (← getConstInfo decl).type
      let some (lhs, _, _) := boundSides? conclusion
        | throwError "`circuit_bound` expects a theorem `m ≤ b` or `m = b` between natural \
            numbers, got{indentExpr conclusion}"
      DiscrTree.mkPath lhs
    boundExt.add (keys, decl) kind
}

end Cslib.Tactic.CircuitBound
