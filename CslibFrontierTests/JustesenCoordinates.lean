/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Justesen

/-! Checked native coordinate decoding and agreement with the indexed code evaluator. -/

set_option linter.privateModule false

namespace CslibFrontierTests.JustesenCoordinates

open Cslib.Code.JustesenFamily Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInSpace

/-- An index in the second half at the second nonzero point. -/
example : decodeIndex 4 14 = ⟨2, 1, 2⟩ := rfl

/-- With a native degree computed from the graph dimensions, the caller decodes one index
in space linear in the binary dimensions and index. -/
example :
    ComputableInSpace (fun ((w, n), index) => decodeIndex (fieldDegree w n) index)
      (encPair (encPair encNat encNat) encNat) encCoordinateNumbers
      (fun p => (encPair (encPair encNat encNat) encNat p).length) := by
  have hdegree := budget_comp_linear fieldDegree_inSpace (fst (encPair encNat encNat) encNat)
  have hindex := snd (encPair encNat encNat) encNat
  exact (budget_comp_linear decodeIndex_inSpace (budget_prod hdegree hindex)).of_enc_eq fun _ => rfl

/-- For a valid index, the native result identifies the same point and bit as rank decoding. -/
example {w n : ℕ} (j : Fin (codeLength w n)) :
    let (point, half, bit) := decodeCoordinate w n j
    decodeIndex (fieldDegree w n) j.val = ⟨point.val + 1, half.val, bit.val⟩ :=
  decodeIndex_eq_decodeCoordinate j

end CslibFrontierTests.JustesenCoordinates
