/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Permanent.ZeroOne
public import CslibFrontier.Computability.Complexity.Classes.SharpP.MetricOracle
public import CslibFrontier.Computability.Complexity.CookLevin.Counting
import CslibFrontier.Computability.Complexity.Problems.Permanent.Membership

/-!
# Integer permanent with a counting satisfiability oracle

[Arora and Barak, Chapter 9, Exercise 2][AroraBarak07] (2007-01-08 draft,
printed p. 185 / PDF p. 201) asks for the integer permanent in `FP^{#SAT}`.
The input `encIntTable` stores binary signed entries; `encIntBin` stores the signed output.
As in Definition 9.5, access to the function oracle means access to its bit graph.
The integer-to-0/1 metric reduction followed by parsimonious Cook–Levin gives one counting
query with polynomial-time recovery; the metric-oracle API reads its polynomially many bits.

## Main results

* `Cslib.Complexity.intPermanent_computableInPolyTimeWithOracle_SharpSAT`: the integer permanent
  is polynomial-time computable relative to the bit graph of `#SAT`.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- **Arora–Barak, Chapter 9, Exercise 2**: the permanent of binary integer tables is in
`FP^{#SAT}`. Tables are interpreted by `tableMatrix`, with dimension the number of rows and
missing entries zero, so this includes every square integer matrix. -/
theorem intPermanent_computableInPolyTimeWithOracle_SharpSAT :
    ComputableInPolyTimeWithOracle (bitGraph encCNF SharpSAT) IntPermanent
      encIntTable encIntBin := by
  have h := metricReducible_intPermanent_zeroOnePermanent.trans
    (CookLevin.SharpSAT_sharpPComplete.2 _ _ ZeroOnePermanent.mem_SharpP).metricReducible
  obtain ⟨p, hp⟩ := SharpP.exists_le_two_pow SharpSAT.mem_SharpP
  refine h.computableInPolyTimeWithOracle (p := p + 1) fun b => ?_
  exact (hp b).trans_lt (Nat.pow_lt_pow_right (by norm_num) (by simp))

end Cslib.Complexity
