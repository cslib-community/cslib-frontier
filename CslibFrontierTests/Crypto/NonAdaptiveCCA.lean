/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.Encryption.CCA.NonAdaptive
import CslibFrontierTests.Crypto.AssumptionNonvacuity

/-! Nonvacuity of non-adaptive 1CCA security (`Encryption.INDCCA1On`): sending the plaintext is not
non-adaptive 1CCA secure. The file is not a `module` because it imports the non-module
`AssumptionNonvacuity`; the module clients are in `NonAdaptiveCCAModule.lean`. -/

namespace CslibFrontierTests.Crypto.NonAdaptiveCCA

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.Encryption Turing.MultiTapeTM
open CslibFrontierTests.Crypto.AssumptionNonvacuity

/-- **Sending the plaintext bit is not non-adaptive 1CCA secure**, for any decryption, since
non-adaptive 1CCA security implies IND-CPA. -/
theorem not_indcca1On_plaintext (decrypt : ℕ → List Bool → List Bool → Option Bool) :
    ¬ INDCCA1On (fun _ _ _ _ => true) encBool encBool emptyKeys plaintext decrypt :=
  fun h => not_indcpa_plaintext h.indcpaOn

end CslibFrontierTests.Crypto.NonAdaptiveCCA
