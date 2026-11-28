/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of the wram_omega tactic)

public import CslibFrontier.Tactic.WramOmega

/-!
# A tagged definition whose body is not exposed

`CslibFrontierTests.WramOmegaTactic` imports this module to check what `wram_omega` reports
about a tagged definition that it cannot unfold. Inside this module the body is visible.
-/

public section

namespace WramOmegaTest

/-- An address whose definition is tagged but not exposed. -/
@[wram_arith] def sealedBase (base : ℕ) : ℕ := base + 7

example {base : ℕ} : base < sealedBase base := by wram_omega

end WramOmegaTest

end
