/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.CarrySave.IteratedQuery
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString

/-! # Native carry-save descent on encoded addresses -/

public section
namespace Cslib.Circuits.Boolean.CarrySaveQuery

open Turing.MultiTapeTM ComputableInPolyTime CarrySaveLocal

/-- Binary height and bit offset with an unframed path and a component selector. -/
enc_structure encQuery : Query where
  path : encBits, remaining : encNat, carry : encBool, bit : encNat

/-- A fixed port updates only the current address. Zero-height and boundary inputs return none. -/
theorem descend_polyTime (j : Fin 7) : ComputableInPolyTime (fun q => descend q j)
    encQuery (encOption encQuery) := by
  have hrem := encQuery_remaining_deg.computableInPolyTime
  have hbit := encQuery_bit_deg.computableInPolyTime
  have hcarry := encQuery_carry_deg.computableInPolyTime
  have hshift := (of_finite (encIn := encBool) (encOut := encNat)
    (fun c => (source c j).shift.val)).comp hcarry
  have hside := (of_finite (encIn := encBool) (encOut := encBits)
    (fun c => [childSide (source c j).word])).comp hcarry
  have hc := (of_finite (encIn := encBool) (encOut := encBool)
    (fun c => childCarry (source c j).word)).comp hcarry
  have hn := encQuery_mk_polyTime (bitsAppend encQuery_path_deg.computableInPolyTime hside)
    (binary_sub' hrem (const 1)) hc (binary_sub' hbit hshift)
  exact (ite' (decide_eq' hrem (const 0)) (const none)
    (ite' (binary_le' hshift hbit) ((optionSome encQuery).comp hn) (const none))).of_enc_eq
    fun q => by simp [descend]

end Cslib.Circuits.Boolean.CarrySaveQuery
