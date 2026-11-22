/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init

/-!
# Scoped rule attributes for `valid_prog` and `prog_frame`

Declares lightweight scoped theorem registries used by `CslibFrontier.Tactic.ValidProg`:

* `@[valid_prog]`: registers admissibility lemmas (`ValidHistory` or wrapper `ValidProg`
  certificates and combinator rules for `pure`, `bind`, `ite`, `dite`).
* `@[prog_rw]`: registers `clientState` / `clientResult` reduction lemmas applied in continuations
  when `valid_prog` steps past a `bind`.
* `@[prog_frame]`: registers `RegionFrame` or read-only `clientState s p = s` lemmas used by
  `prog_frame`.
* `prog_cost`: `simp` attribute of `memoryCost` equations used by `prog_cost`.

## Main definitions

* `Cslib.Tactic.ValidProg.validProgExt`, `Cslib.Tactic.ValidProg.progRwExt`,
  `Cslib.Tactic.ValidProg.progFrameExt`: scoped rule extensions.
* `prog_cost`: `simp` attribute for `memoryCost` rules.
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

/-- Theorems registered with `@[prog_rw]`. -/
initialize progRwExt : SimpleScopedEnvExtension Name (Array Name) ←
  registerNameListAttr `Cslib.Tactic.ValidProg.progRwExt `prog_rw
    "Register a `clientState`/`clientResult` reduction lemma for `valid_prog`."

/-- Theorems registered with `@[prog_frame]`. -/
initialize progFrameExt : SimpleScopedEnvExtension Name (Array Name) ←
  registerNameListAttr `Cslib.Tactic.ValidProg.progFrameExt `prog_frame
    "Register a `RegionFrame` or `clientState` preservation lemma for `prog_frame`."

end Cslib.Tactic.ValidProg

/-- Simp set of `memoryCost` equations for `prog_cost`. -/
register_simp_attr prog_cost
