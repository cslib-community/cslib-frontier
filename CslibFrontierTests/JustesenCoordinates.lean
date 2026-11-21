/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Justesen

/-! Checked native coordinate decoding, point words and agreement with the indexed evaluator. -/

set_option linter.privateModule false

namespace CslibFrontierTests.JustesenCoordinates

open Cslib.Code.JustesenFamily Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInSpace

/-- An index in the second half at the second nonzero point. -/
example : decodeIndex 4 14 = ⟨2, 1, 2⟩ := rfl

/-- For a valid index, the native result identifies the same point and bit as rank decoding. -/
example {w n : ℕ} (j : Fin (codeLength w n)) :
    let (point, half, bit) := decodeCoordinate w n j
    decodeIndex (fieldDegree w n) j.val = ⟨point.val + 1, half.val, bit.val⟩ :=
  decodeIndex_eq_decodeCoordinate j

/-- The second point's coefficient word is little-endian and padded to the field degree. -/
example : Cslib.BitString.lowBits 4 (decodeIndex 4 14).point = [false, true, false, false] := rfl

/-- The native caller can retain the point word next to the half and bit of the numeric decoder. -/
example :
    ComputableInSpace
      (fun (p : (ℕ × ℕ) × ℕ) =>
        let degree := fieldDegree p.1.1 p.1.2
        let coord := decodeIndex degree p.2
        (Cslib.BitString.lowBits degree coord.point, coord))
      (encPair (encPair encNat encNat) encNat) (encPair (encList encBool) encCoordinateNumbers)
      (fun p => (encPair (encPair encNat encNat) encNat p).length) := by
  have hdegree := budget_comp_linear fieldDegree_inSpace (fst (encPair encNat encNat) encNat)
  have hindex := snd (encPair encNat encNat) encNat
  have hcoord := budget_comp_linear decodeIndex_inSpace (budget_prod hdegree hindex)
  exact budget_prod decodePointWord_inSpace hcoord

/-- The evaluator consumes exactly the word produced from the decoded point number. -/
example {w n : ℕ} (j : Fin (codeLength w n)) :
    List.ofFn (nonzeroPointBits (decodeCoordinate w n j).1) =
      Cslib.BitString.lowBits (fieldDegree w n) (decodeIndex (fieldDegree w n) j.val).point :=
  (lowBits_decodeIndex_point j).symm

end CslibFrontierTests.JustesenCoordinates
