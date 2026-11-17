/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.SAT.ExactOne.GeometryData
public import CslibFrontier.Computability.Complexity.Problems.SAT.Geometry
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.Fintype.Pi

/-!
# Continuous geometry certificates for exact-one gadgets

`disjunctionGeometry_check`, `falseGeometry_check` and `complementGeometry_check`
instantiate the shared `SAT.LocalGeometry.Check` for the fixed exact-one drawings.
Composition with an input drawing is a separate construction.

## References

The incidence graphs are from [HuntMaratheRadhakrishnanStearns1998, Theorem 3.8,
Figures 3.4–3.5 and Lemma 3.6]. The orthogonal certificates are original.
-/

public section

namespace Cslib.Complexity.SAT.ExactOne

open Orthogonal

/-- Complete finite certificate for the parsimonious disjunction replacement. -/
theorem disjunctionGeometry_check : LocalGeometry.Check disjunctionGeometry := by
  decide +kernel

/-- Complete finite certificate for the positive forced-false gadget. -/
theorem falseGeometry_check : LocalGeometry.Check falseGeometry := by
  decide +kernel

/-- Complete finite certificate for the positive complement gadget. -/
theorem complementGeometry_check : LocalGeometry.Check complementGeometry := by
  decide +kernel

end Cslib.Complexity.SAT.ExactOne
