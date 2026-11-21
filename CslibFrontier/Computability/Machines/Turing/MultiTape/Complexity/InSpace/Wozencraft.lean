/-
Copyright (c) 2026 Christian Reitwiessner, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
public import CslibFrontier.Foundations.Data.Code.Justesen
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.BitList
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.ListSlice
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure

/-!
# Wozencraft bit selection in native space

An evaluated coefficient word is the first half of the inner code. The second half is its
product with the field point. With a native multiplication using the retained field context,
a binary half and bit index suffice to read a coordinate in linear space.

## Main results

* `Turing.Wozencraft.bitWith_inSpace`: native bit selection given the multiplication certificate.
-/

public section

namespace Turing.Wozencraft

open MultiTapeTM MultiTapeTM.ComputableInSpace
open Cslib.Code

/-- One bit query to the Wozencraft inner code after polynomial evaluation. -/
structure BitInput (Context : Type) where
  /-- Retained multiplication parameters, such as the modulus word. -/
  context : Context
  /-- The evaluation point as a coefficient word. -/
  point : List Bool
  /-- The polynomial value at the point, in the same coefficient order. -/
  evaluation : List Bool
  /-- Zero for the evaluation half, or one for the product half. -/
  half : ℕ
  /-- The binary index within the selected half. -/
  bit : ℕ

variable {Context : Type}

/-- Multiplication context, two framed Boolean lists and the binary half are framed fields.
The binary bit index comes last. -/
enc_structure encBitInput (encContext : Context ↪ List Bool) : BitInput Context where
  context : encContext, point : (encList encBool), evaluation : (encList encBool),
  half : encNat, bit : encNat

/-- Read one bit of the inner code in space linear in the encoded request, using the supplied
multiplication certificate on the two coefficient words and their retained context. -/
theorem bitWith_inSpace {encContext : Context ↪ List Bool}
    {mul : Context → List Bool → List Bool → List Bool}
    (hmul : ComputableInSpace
      (fun p : Context × List Bool × List Bool => mul p.1 p.2.1 p.2.2)
      (encPair encContext (encPair (encList encBool) (encList encBool))) (encList encBool)
      (fun p => (encPair encContext (encPair (encList encBool) (encList encBool)) p).length)) :
    ComputableInSpace
      (fun p : BitInput Context =>
        wozencraftBitWith (mul p.context) p.point p.evaluation p.half p.bit)
      (encBitInput encContext) encBool (fun p => (encBitInput encContext p).length) := by
  have h := budget_id (BigOLe.refl fun p => (encBitInput encContext p).length)
  have hctx := encBitInput_context_budget encContext h
  have hp := encBitInput_point_budget encContext h
  have ha := encBitInput_evaluation_budget encContext h
  have hzero := budget_natIsZero (encBitInput_half_budget encContext h)
  have hprod := budget_comp_linear hmul (budget_prod hctx (budget_prod hp ha))
  have hword := budget_comp_linear listToBits (budget_ite hzero ha hprod)
  have hbit := encBitInput_bit_budget encContext h
  exact (budget_comp_linear (bitsGetD false) (budget_prod hword hbit)).of_enc_eq fun p => by
    simp only [wozencraftBitWith, decide_eq_true_eq]

end Turing.Wozencraft
