/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.CommunityDetection.Cleanup
public import CslibFrontier.Algorithms.IntegerPower.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Integer-power community recovery

The algorithm has two fixed natural parameters: a resolution `D` and a centering numerator `c`.
It forms the symmetric integer matrix with zero diagonal and off-diagonal entries
`D² Aᵢⱼ - c`. The shared finite power search tests growth at threshold `D n`, rounds the returned
integer vector to signs, and performs one weighted-vote cleanup using the same matrix.

These are mathematical definitions. `Program` proves exact agreement with a native list program
on the common dense graph encoding, including inputs for which the search uses its zero fallback.
The probability analysis chooses the two integer parameters once for each fixed real pair
of edge probabilities; the program never takes real numbers as input.
-/

public section

namespace Cslib.Algorithms.CommunityDetection

/-- Fixed integer constants for matrix centering and the power-search threshold. -/
structure PowerParameters where
  /-- `D`: matrix entries are scaled by `D²`, and the growth threshold is `D n`. -/
  resolution : ℕ
  /-- The integer subtracted from each off-diagonal scaled adjacency entry. -/
  center : ℕ
  deriving DecidableEq, Repr, Inhabited

variable {n : ℕ}

/-- An exactly represented centered adjacency matrix with zero diagonal. -/
@[expose] def integerMatrix (params : PowerParameters) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => if i = j then 0 else
    if G.Adj i j then (params.resolution : ℤ) ^ 2 - params.center else -(params.center : ℤ)

/-- Round the stored power-search vector to community labels. Negative coordinates mean `true`,
and zero coordinates mean `false`. -/
@[expose] noncomputable def powerLabels (params : PowerParameters) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] : Fin n → Bool :=
  BitString.signRound fun i =>
    (IntegerPower.recoveredVector (integerMatrix params G) (params.resolution * n) i : ℝ)

/-- Recover community labels by integer power search, sign rounding, and one weighted vote. -/
@[expose] noncomputable def recoverPower (params : PowerParameters) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] : Fin n → Bool :=
  cleanup ((integerMatrix params G).map (Int.castRingHom ℝ)) (powerLabels params G)

end Cslib.Algorithms.CommunityDetection
