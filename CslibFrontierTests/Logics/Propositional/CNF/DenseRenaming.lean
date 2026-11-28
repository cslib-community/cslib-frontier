/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Logics.Propositional.CNF.DenseRenaming
import CslibFrontier.Logics.Propositional.CNF.LRATRelabel
public meta import CslibFrontier.Logics.Propositional.CNF.DenseRenaming

/-!
# Renaming variables to `0, …, k - 1`

The formula `[[], [(10⁹, true)]]` has one variable, which the renaming sends to `0`; the map back
sends `0` to `10⁹`. On `x₇ ∧ ¬x₇ ∨ x₃`, the variables `7` and `3` become `0` and `1`, in order of
first occurrence, and renaming back gives the formula again. An LRAT refutation of `x₅`, `¬x₅`
is accepted, and so is its renaming along an injective map, for the renamed formula.
-/

set_option linter.hashCommand false
set_option linter.privateModule false

namespace CslibFrontierTests.Logics.Propositional.CNF.DenseRenaming

open Cslib.Logic.PL
open Std.Tactic.BVDecide (LRAT.IntAction)

#guard (CNF.denseRenaming [[], [((1000000000 : ℕ), true)]]).size == 1
#guard (CNF.denseRenaming [[], [((1000000000 : ℕ), true)]]).toDense 1000000000 == 0
#guard (CNF.denseRenaming [[], [((1000000000 : ℕ), true)]]).fromDense 0 == 1000000000

private abbrev ψ : CNF ℕ := [[(7, true)], [(7, false), (3, true)]]

#guard (ψ.relabel (CNF.denseRenaming ψ).toDense) == [[(0, true)], [(0, false), (1, true)]]
#guard ((ψ.relabel (CNF.denseRenaming ψ).toDense).relabel (CNF.denseRenaming ψ).fromDense) == ψ

private abbrev contra : CNF ℕ := [[(5, true)], [(5, false)]]

private abbrev cert : Array LRAT.IntAction := #[.addEmpty 3 #[1, 2]]

example : contra.checkLRAT cert = true := by decide

-- The checker accepts the certificate renamed along the injective map `v ↦ v + 2`.
example : (contra.relabel (· + 2)).checkLRAT (cert.map (relabelAction (· + 2))) = true := by
  rw [CNF.checkLRAT_relabel (fun _ _ h => by simpa using h)]
  decide

end CslibFrontierTests.Logics.Propositional.CNF.DenseRenaming
