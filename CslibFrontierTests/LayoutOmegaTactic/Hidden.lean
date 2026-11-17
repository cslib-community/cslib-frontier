/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of the layout_omega tactic)

public import CslibFrontier.Tactic.LayoutOmega

/-!
# A layout definition whose body is not exposed

`CslibFrontierTests.LayoutOmegaTactic` imports this module to check what `layout_omega` reports
about a tagged definition that it cannot unfold. Inside this module the body is visible.
-/

public section

namespace LayoutOmegaTest

/-- An address whose definition is tagged but not exposed. -/
@[layout] def sealedBase (base : ℕ) : ℕ := base + 7

example {base : ℕ} : base < sealedBase base := by layout_omega

end LayoutOmegaTest

end
