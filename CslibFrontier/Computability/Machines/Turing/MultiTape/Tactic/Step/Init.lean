/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init

/-!
# The simp set of `tm_step`

The simp set used by `tm_step` in
`CslibFrontier.Computability.Machines.Turing.MultiTape.Tactic.Step`, declared in a file of its own
because an attribute cannot be used in the file declaring it.

## Main definitions

* `tm_step_simps`: the fields of a configuration after an action, and the values of tapes written
  with `Function.update`, `Fin.lastCases`, `Fin.addCases` and `Fin.append` at the indices `tm_step`
  splits on.
-/

public meta section

/-- The simp set `tm_step_simps` computes the fields of a multi-tape configuration after an action
(`Turing.Action.apply`), and the values of families of tapes written with `Function.update`,
`Fin.lastCases`, `Fin.addCases` and `Fin.append` at the indices `tm_step` splits on. Tag the
projection lemmas of a configuration builder with it to have `tm_step` use them. -/
register_simp_attr tm_step_simps

end
