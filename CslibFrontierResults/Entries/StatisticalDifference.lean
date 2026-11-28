/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Computability.Complexity.Classes.SZK.ArthurMerlin
import CslibFrontier.Computability.Complexity.Classes.SZK.CoArthurMerlin

/-!
# Arthur–Merlin protocols for languages reducing to Statistical Difference

The source states its class containments for interactive statistical zero knowledge. These
entries cover languages equipped with a polynomial-time reduction of their total promise to
Statistical Difference. The equivalence of the two formulations is tracked in
[#3205](https://github.com/cslib-community/cslib-frontier/issues/3205).
-/

register_result "statistical-difference-languages-subset-am" where
  title := "Languages reducing to Statistical Difference belong to AM"
  topic := "interactive proofs"
  sources := [
    { paper := SahaiVadhan2003, theorem := "Protocol for Statistical Difference",
      locator := "JACM 2003, §3.3, pp. 212–213" }
  ]
  theorems := [Cslib.Complexity.SZK_subset_AM]
  scope := "For any encoding, a total language reducing to the Statistical Difference promise \
    with thresholds 2/3 and 1/3 has an AM protocol. The verifier uses the guessing game \
    followed by a private-coin to public-coin simulation. The interactive SZK equivalence \
    remains open in the library."

register_result "statistical-difference-languages-subset-coam" where
  title := "Languages reducing to Statistical Difference belong to coAM"
  topic := "interactive proofs"
  sources := [
    { paper := SahaiVadhan2003,
      theorem := "Corollary 4.5 specialized to Statistical Difference (coAM direction)",
      locator := "JACM 2003, §4.2, p. 220" }
  ]
  theorems := [Cslib.Complexity.SZK_subset_coAM]
  scope := "For any encoding, the complement of a total language reducing to the Statistical \
    Difference promise at thresholds 2/3 and 1/3 has an AM protocol. The formalization \
    uses weighted hash tests for overlap. The interactive SZK equivalence remains open in the \
    library."
