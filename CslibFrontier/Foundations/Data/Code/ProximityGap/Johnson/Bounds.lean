/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.Code.SudanInterpolant

/-!
# Degree Budgets and Exceptional-Set Bounds for Johnson-Bound Proximity Gaps

Core exposed arithmetic parameters shared by the Johnson-bound correlated-agreement pipeline
and the asymptotic parameter bounds module.

## Main definitions

* `Cslib.Code.ProximityGap.maxYDeg`: maximum `Y`-degree in `Sudan.monomials d D`.
* `Cslib.Code.ProximityGap.siegelZDeg`: explicit `Z`-degree budget for zero-denominator Siegel
  interpolation along a degree-`r` curve.
* `Cslib.Code.ProximityGap.johnsonCurveBound`: explicit `|F|`-independent upper bound on
  exceptional scalars for Johnson-bound weighted correlated agreement.
-/

namespace Cslib.Code.ProximityGap

open Cslib.Code Finset

@[expose] public section

/-- Maximum `Y`-degree among monomials `(a, b)` in `Sudan.monomials d D`. -/
def maxYDeg (d D : ℕ) : ℕ :=
  (Sudan.monomials d D).sup Prod.snd

/-- Explicit `Z`-degree budget for zero-denominator Siegel interpolation of a degree-`r` curve. -/
def siegelZDeg (n m d D r : ℕ) : ℕ :=
  let R_eq := n * (m * (m + 1) / 2)
  let C_mon := #(Sudan.monomials d D)
  (R_eq * r * maxYDeg d D) / (C_mon - R_eq)

/-- Explicit `|F|`-independent upper bound on exceptional scalars for Johnson-bound weighted
correlated agreement on degree-`r` curves. -/
def johnsonCurveBound (n m d D r W_tot : ℕ) : ℕ :=
  let D_Y := maxYDeg d D
  let B_Z := siegelZDeg n m d D r
  B_Z + 2 * D_Y * (D + B_Z) + W_tot * D_Y ^ 2 * (4 * D * B_Z + r * D_Y)

end

end Cslib.Code.ProximityGap
