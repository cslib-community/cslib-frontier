/-
Copyright (c) 2026 Uladzislau Artsemyeu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uladzislau Artsemyeu
-/

import CslibFrontier.Computability.MCSP.Restrictions
import CslibFrontier.Computability.MCSP.CommunicationCut

/-!
# Tests for quadratic MCSP lower bounds and communication cuts

Checks the finite gate bound at arity `16` and the `512`-bit equality, protocol-depth, and
crossing-wire lower bounds at arity `32`.
-/

namespace Cslib.MCSP.Tests.MCSPLowerBounds

open Cslib.Circuits Cslib.Circuits.Boolean Cslib.Communication
open Cslib.MCSP.Restrictions Cslib.MCSP.CommunicationCut

example : 119255 ≤ complexity interpretation (single (mcspSquare 16)) :=
  mcspSquare_sixteen_lower_bound

example :
    ∃ h : BooleanFunction 22,
      ∀ p : Protocol (BooleanFunction 9) (BooleanFunction 9) Bool,
        p.run = mixedTest h → 513 ≤ p.depth := by
  obtain ⟨h, hEq⟩ := mcspSquare_32_equality_cut
  exact ⟨h, fun p hp => protocol_depth_lower_bound h hEq p hp⟩

example :
    ∃ h : BooleanFunction 22,
      ∀ (c : Circuit signature (2 ^ 32) 1)
        (_ : c.Computes interpretation (single (mcspSquare 32)))
        (owner : Wire (2 ^ 32) c.size → Bool) (_ : ∀ i, owner (.input i) = mask 9 h i),
        512 ≤ (crossingWires c.program owner).card :=
  mcspSquare_32_crossing_cut

end Cslib.MCSP.Tests.MCSPLowerBounds
