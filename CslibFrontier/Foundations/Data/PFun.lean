/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Data/PFun.lean`)

public import CslibFrontier.Init
public import Mathlib.Data.PFun

/-!
# Binds into partial functions

Under the module system the body of `PFun` is not exposed, so `simp` does not see a partial
function `f : α →. β` as a function `α → Part β`. A bind `x >>= f` into a partial function is then
out of reach of Mathlib's `Part.bind` lemmas. `Part.bind_pfun` rewrites it to the eta-expanded
`x.bind fun y => f y`, to which they apply.
-/

public section

namespace Part

universe u

/-- A bind into a partial function, eta-expanded, so that Mathlib's `Part.bind` lemmas apply. -/
theorem bind_pfun {α β : Type u} (x : Part α) (f : α →. β) : x >>= f = x.bind fun y => f y := rfl

end Part
