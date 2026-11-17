/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init

/-!
# The attribute `layout`

Declares the attribute `@[layout]`, in a file of its own because an attribute cannot be used in the
file declaring it, and so that a module defining a memory layout can tag its definitions without
importing the tactic `layout_omega` of `CslibFrontier.Tactic.LayoutOmega`, which reads the tags.

## Main definitions

* `layout`: marks a definition of an address, a size or an arithmetic predicate as one that
  `layout_omega` unfolds.
-/

public meta section

namespace Cslib.Tactic.LayoutOmega

open Lean Meta Elab

/-- What a `@[layout]` definition returns once applied to all its arguments. -/
inductive Kind where
  /-- A natural number or an integer: `layout_omega` unfolds each application. -/
  | number
  /-- A proposition: `layout_omega` unfolds it in the goal and in the hypotheses. -/
  | predicate
  deriving Inhabited, BEq

/-- The definitions tagged `@[layout]`, each with what it returns. -/
initialize layoutExt : SimpleScopedEnvExtension (Name × Kind) (NameMap Kind) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun layouts (name, kind) => layouts.insert name kind
    initial := {}
  }

/-- What the definition `declName` returns, if `@[layout]` accepts it: `ℕ`, `ℤ` or `Prop`, after
all the arguments its type names. -/
private def layoutKind? (declName : Name) : MetaM (Option Kind) := do
  forallTelescope (← getConstInfo declName).type fun _ result => do
    let result ← whnfR result
    if result.isConstOf ``Nat || result.isConstOf ``Int then return some .number
    if result.isProp then return some .predicate
    return none

/-- `@[layout]` marks a definition as part of a memory layout: an address, an offset or a size
(a definition returning `ℕ` or `ℤ`), or a predicate comparing such numbers (a definition returning
`Prop`). `layout_omega` unfolds the tagged definitions it meets, so that a proof about a layout
does not list them. Tag the definition where it is written, `@[layout] def tableBase …`, or later
with `attribute [layout] tableBase`; use `attribute [local layout]` for a private definition.

The definition's body must be visible where `layout_omega` is called: the definition is exposed,
or the call is in its module. The tag does not expose the body and adds no `simp` lemma. -/
syntax (name := layout) "layout" : attr

initialize registerBuiltinAttribute {
  name := `layout
  descr := "a layout definition, which `layout_omega` unfolds"
  applicationTime := .afterTypeChecking
  add := fun declName stx kind => do
    unless stx.isOfKind ``layout do throwUnsupportedSyntax
    -- The body of a definition that is not exposed is visible in its own module only.
    let result ← withoutExporting do
      unless (← getConstInfo declName).hasValue do
        throwError "@[layout]: `{.ofConstName declName}` is not a definition whose body is \
          visible here, so `layout_omega` could not unfold it."
      if ← isRecursiveDefinition declName then
        throwError "@[layout]: `{.ofConstName declName}` is defined by recursion, so it has no \
          body that `layout_omega` could unfold."
      let some result ← MetaM.run' (layoutKind? declName)
        | throwError "@[layout]: `{.ofConstName declName}` returns neither a natural number, an \
            integer nor a proposition; `layout_omega` reasons by linear arithmetic over `ℕ` and \
            `ℤ`."
      pure result
    layoutExt.add (declName, result) kind
}

end Cslib.Tactic.LayoutOmega

end
