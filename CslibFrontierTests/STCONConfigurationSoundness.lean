/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Complexity.Problems.STCON.Reduction

/-! # Soundness of the configuration instance at every radix

A path to the sink of `STCON.configurationInstance ntm c w` is an accepting computation of `ntm`
for every `c`, with no space bound on the machine. Consequently two machines that never accept
the same word never both have a reachable instance on it, whatever the two radix exponents. A
search over growing radices can therefore stop at the first positive verdict.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.STCONConfigurationSoundness

open Turing Cslib.Complexity

/-- At the smallest radix exponent, and for a machine with no space bound, reachability in the
instance still gives acceptance. -/
example {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State) (w : List Bool)
    (h : STCON.configurationInstance ntm 0 w ∈ STCON) : ntm.Accepts w :=
  STCON.accepts_of_configurationInstance_mem ntm 0 h

/-- Machines that never accept the same word never both have a reachable instance on it, at any
pair of radix exponents. -/
example {k k' : ℕ} {State State' : Type} [Fintype State] [Fintype State']
    (ntm : MultiTapeNTM k Bool State) (ntm' : MultiTapeNTM k' Bool State') (w : List Bool)
    (hdisjoint : ¬(ntm.Accepts w ∧ ntm'.Accepts w)) (c c' : ℕ) :
    ¬(STCON.configurationInstance ntm c w ∈ STCON ∧
      STCON.configurationInstance ntm' c' w ∈ STCON) :=
  fun h => hdisjoint ⟨STCON.accepts_of_configurationInstance_mem ntm c h.1,
    STCON.accepts_of_configurationInstance_mem ntm' c' h.2⟩

end CslibFrontierTests.STCONConfigurationSoundness
