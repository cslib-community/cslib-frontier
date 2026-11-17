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
premise holds for #SAT (Theorem 9.7, through metric completeness) at every instance encoding, and
`encCNF` has a decoder, so a polynomial-time algorithm for #SAT would give `#P = FP` at every
instance encoding. On `{0,1}*` the theorem takes Definition 9.5's word-domain premise directly. -/

set_option linter.privateModule false

namespace CslibFrontierTests.SharpPOracleCollapse

open Cslib.Complexity Turing.MultiTapeTM

/-- Proposition 9.6 for `#SAT` under `encCNF`. -/
example (h : ComputableInPolyTime SharpSAT encCNF encNat) {α : Type} {enc : α ↪ List Bool}
    {f : α → ℕ} : f ∈ SharpP enc ↔ ComputableInPolyTime f enc encNat :=
  mem_SharpP_iff_computableInPolyTime_of_bitGraph (.list (.list (.pair .nat .bool)))
    (fun _ hf =>
      CookLevin.SharpSAT_sharpPComplete.sharpPMetricComplete.computableInPolyTimeWithOracle hf) h

/-- Proposition 9.6 on `{0,1}*`, from Definition 9.5's premise for word functions: if every #P
function on words is in `FP^g` for a polynomial-time `g` on words, then #P = FP on words. -/
example {g : List Bool → ℕ}
    (hcomplete : ∀ f : List Bool → ℕ, f ∈ SharpP encBits →
      ComputableInPolyTimeWithOracle (bitGraph encBits g) f encBits encNat)
    (hg : ComputableInPolyTime g encBits encNat) {f : List Bool → ℕ} :
    f ∈ SharpP encBits ↔ ComputableInPolyTime f encBits encNat :=
  mem_SharpP_iff_computableInPolyTime_of_bitGraph .bits hcomplete hg

/-- The bit graph of `#SAT` is decided in polynomial time once `#SAT` is. -/
example (h : ComputableInPolyTime SharpSAT encCNF encNat) : bitGraph encCNF SharpSAT ∈ P encBits :=
  bitGraph_mem_P (.list (.list (.pair .nat .bool))) h

end CslibFrontierTests.SharpPOracleCollapse
