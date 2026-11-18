/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Crypto.Computational.MLDSA.QuantumKeyOnly

/-! Byte-register conventions for the coherent ML-DSA key-only verifier. -/

set_option linter.privateModule false

open Cslib.Crypto Cslib.Crypto.MLDSA.FIPS204
open Cslib.Crypto.MLDSA.FIPS204.QuantumKeyOnly

-- FIPS 204, Table 1 and Algorithm 28. The address is μ followed by w₁Encode.
example : [Level.mlDSA44, .mlDSA65, .mlDSA87].map commitmentInputWidth =
    [6656, 6656, 8704] := by decide

-- Both byte positions and bit significance matter to coherent XOR queries.
example : (registerBytes 2 (fun i => decide (i.val = 7 ∨ i.val = 8))).toList =
    [128, 1] := by decide
