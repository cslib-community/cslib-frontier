/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Complexity.Classes.SharpP.MetricOracle
import CslibFrontier.Computability.Complexity.CookLevin.Counting

/-! Checked clients of Arora–Barak, Proposition 9.6
(`Cslib.Complexity.mem_SharpP_iff_computableInPolyTime_of_bitGraph`). The Definition 9.5
hypothesis holds for #SAT (Theorem 9.7, through metric completeness), and `encCNF` has a decoder,
so a polynomial-time algorithm for #SAT would give `#P = FP` at every instance encoding. -/

set_option linter.privateModule false

namespace CslibFrontierTests.SharpPOracleCollapse

open Cslib.Complexity Turing.MultiTapeTM

/-- Proposition 9.6 for `#SAT` under `encCNF`. -/
example (h : ComputableInPolyTime SharpSAT encCNF encNat) {α : Type} {enc : α ↪ List Bool}
    {f : α → ℕ} : f ∈ SharpP enc ↔ ComputableInPolyTime f enc encNat :=
  mem_SharpP_iff_computableInPolyTime_of_bitGraph (.list (.list (.pair .nat .bool)))
    (fun _ _ hf =>
      CookLevin.SharpSAT_sharpPComplete.sharpPMetricComplete.computableInPolyTimeWithOracle hf) h

/-- The bit graph of `#SAT` is decided in polynomial time once `#SAT` is. -/
example (h : ComputableInPolyTime SharpSAT encCNF encNat) : bitGraph encCNF SharpSAT ∈ P encBits :=
  bitGraph_mem_P (.list (.list (.pair .nat .bool))) h

end CslibFrontierTests.SharpPOracleCollapse
