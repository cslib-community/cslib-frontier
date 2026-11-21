/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.ConvolutionOperand
public import CslibFrontier.Foundations.Data.BitString.List.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryLog

/-! # Native extraction of both indices from one physical convolution path -/

public section
namespace Cslib.ConvolutionOperand

open Turing.MultiTapeTM ComputableInPolyTime

/-- The path tape carries a row prefix followed by a partial-product shift. -/
structure PathInput where
  /-- Number of coefficients. -/
  degree : ℕ
  /-- Number of bits per coefficient. -/
  precision : ℕ
  /-- Requested convolution diagonal. -/
  diagonal : ℕ
  /-- Physical path, most-significant bit first in each field. -/
  path : List Bool
  /-- Output position in the selected carry-save leaf. -/
  bit : ℕ
  /-- Select the zero carry word when true. -/
  carry : Bool
  /-- Select the second operand when true. -/
  right : Bool

/-- The only field proportional to the traversal length is the raw path. -/
enc_structure encPathInput : PathInput where
  degree : encNat, precision : encNat, diagonal : encNat, path : encBits,
  bit : encNat, carry : encBool, right : encBool

/-- The path is split at the exact depth of the row-selection tree. -/
@[expose] def unpack (a : PathInput) : Input :=
  let L := Nat.clog 2 a.degree
  ⟨a.degree, a.precision, a.diagonal, BitString.binaryValue (a.path.take L),
    BitString.binaryValue (a.path.drop L), a.bit, a.carry, a.right⟩

/-- Decoding and operand selection are polynomial in the binary parameters and path length. -/
theorem computableInPolyTime_path :
    ComputableInPolyTime (run ∘ unpack) encPathInput (encOption (encPair encNat encNat)) := by
  have hd := encPathInput_degree_deg.computableInPolyTime
  have hp := encPathInput_path_deg.computableInPolyTime
  have hL := binary_clog_two.comp hd
  exact computableInPolyTime_run.comp (encInput_mk_polyTime hd
    encPathInput_precision_deg.computableInPolyTime encPathInput_diagonal_deg.computableInPolyTime
    (bitsBinaryValue.comp (bitsTakeWithInput hp hL))
    (bitsBinaryValue.comp (bitsDropWithInput hp hL))
    encPathInput_bit_deg.computableInPolyTime encPathInput_carry_deg.computableInPolyTime
    encPathInput_right_deg.computableInPolyTime)

end Cslib.ConvolutionOperand
