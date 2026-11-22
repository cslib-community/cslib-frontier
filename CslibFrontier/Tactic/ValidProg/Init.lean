/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init

/-!
# Scoped rule attribute for `valid_prog`

Declares the lightweight scoped theorem registry `@[valid_prog]` used by
`CslibFrontier.Tactic.ValidProg` to register admissibility lemmas (`ValidHistory` or wrapper
`ValidProg` certificates and combinator rules for `pure`, `bind`, and `ite`).

## Main definitions

* `Cslib.Tactic.ValidProg.validProgExt`: scoped rule extension for `@[valid_prog]`.
-/

public meta section

namespace Cslib.Tactic.ValidProg

open Lean

/-- Rule registry preserving insertion order and honoring `local`/`scoped` attributes. -/
private def registerNameListAttr (extName attrName : Name) (descr : String) :
    IO (SimpleScopedEnvExtension Name (Array Name)) := do
  let ext ← registerSimpleScopedEnvExtension {
    name := extName
    addEntry := fun arr n => if arr.contains n then arr else arr.push n
    initial := #[]
  }
  registerBuiltinAttribute {
    name := attrName
    descr := descr
    applicationTime := .afterTypeChecking
    add := fun decl _ kind => do
      let scope := match kind with
        | .local => .local
        | .scoped => .scoped
        | .global => .global
      ext.add decl scope
  }
  return ext

/-- Theorems registered with `@[valid_prog]`. -/
initialize validProgExt : SimpleScopedEnvExtension Name (Array Name) ←
  registerNameListAttr `Cslib.Tactic.ValidProg.validProgExt `valid_prog
    "Register an admissibility lemma for the `valid_prog` tactic."

end Cslib.Tactic.ValidProg
