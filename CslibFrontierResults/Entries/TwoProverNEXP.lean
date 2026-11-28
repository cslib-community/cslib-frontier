/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Computability.Complexity.Classes.MIP

/-! # The two-prover characterization of nondeterministic exponential time -/

register_result "babai-fortnow-lund-two-prover-nexp" where
  title := "Two-prover interactive proofs characterize nondeterministic exponential time"
  topic := "interactive proofs"
  sources := [
    { paper := BabaiFortnowLund1991, theorem := "Theorem 1.1",
      locator := "Computational Complexity 1 (1991), p. 4; §2, pp. 6–8; §3.4, p. 13" }
  ]
  theorems := [Cslib.Complexity.MIP₂_eq_NEXP, Cslib.Complexity.MIP_eq_NEXP]
  scope := "For every fixed input encoding, a strict polynomial-time private-coin verifier \
    with two classical noncommunicating provers recognizes exactly nondeterministic exponential \
    time. Lean uses completeness 2/3 and soundness 1/3. The paper gives amplified error bounds. \
    The equality also holds for the class allowing a constant number of provers per language."
