/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.UC.Functionality.Commitment
public import CslibFrontier.Crypto.Protocols.UC.Impossibility.Commitment

/-!
# Ideal UC Bit Commitment and Canetti–Fischlin Plain-Model Impossibility

Umbrella module re-exporting the ideal bit-commitment functionality `fcom` and plain-model
commitment scheme interface (`CslibFrontier.Crypto.Protocols.UC.Functionality.Commitment`)
together with the statistical, call-bounded special case of the Canetti–Fischlin plain-model
impossibility theorem (`CslibFrontier.Crypto.Protocols.UC.Impossibility.Commitment`,
[CanettiFischlin2001], Theorem 6) for backward compatibility.
-/
