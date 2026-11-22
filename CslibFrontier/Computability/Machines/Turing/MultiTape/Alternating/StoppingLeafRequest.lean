/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CountingLeaf.Raw
public import
CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContraction.StoppingQuery.RouteTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.BitString.Cut
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Envelope

/-!
# Preparing a stopping-product leaf from a streamed sum

The six physical fields have exactly the counting-leaf serializer's encoding. Its context stores
only the product parameters and coefficient. Preparation copies the assignment path unchanged
and computes a product-root position from at most the precision's binary length of index digits.

The native instruction has a linear charge for the complete raw query and polynomial work only
in the short context. Thus arbitrary padding on count, width, path or index words never enters a
polynomial power. Carry components and out-of-range capped indices select the constant-zero leaf.
The capped index equals the original index whenever the latter is below the stated precision.
-/

noncomputable section

public section

namespace Turing.MultiTapeATM.StoppingLeafRequest

open MultiTapeTM Cslib Cslib.BitString ComputableInPolyTime
open Cslib.Circuits.Frontier.FastContraction.StoppingQuery Product ProductRouting

/-- Binary product parameters and the binary coefficient shared by all sum leaves. -/
structure Context where
  /-- Extension-ring scale, precision, and vertex count. -/
  parameters : Parameters
  /-- Representative coefficient summed over all assignments. -/
  coefficient : ℕ
  deriving DecidableEq

/-- A framed binary parameter record followed by the binary coefficient. -/
enc_structure encContext : Context where parameters : encParameters, coefficient : encNat

/-- The counting serializer's fields, with its context interpreted as product metadata. -/
structure Input where
  /-- Short parameters shared by every assignment leaf. -/
  context : Context
  /-- Raw little-endian count word retained by the physical serializer. -/
  count : List Bool
  /-- Raw little-endian precision word retained by the physical serializer. -/
  width : List Bool
  /-- Most-significant-first assignment path. -/
  path : List Bool
  /-- Select the constant-zero second carry-save component when true. -/
  carry : Bool
  /-- Raw little-endian bit index, possibly with redundant high zeroes. -/
  bit : List Bool

/-- Five framed fields followed by the raw little-endian bit index. Long words stay raw. -/
enc_structure encInput : Input where
  context : encContext, count : encBits, width : encBits, path : encBits,
  carry : encBool, bit : encBits

/-- The typed view retains every cell of the existing raw serializer output. -/
theorem encInput_eq (x : Input) : encInput x = CountingLeaf.encRawInput
    ⟨encContext x.context, x.count, x.width, x.path, x.carry, x.bit⟩ := rfl

/-- Two words for the product runner: the opaque assignment and the short Boolean position. -/
structure Prepared where
  /-- Unchanged raw assignment path for the protected product tape. -/
  assignment : List Bool
  /-- Encoded root gate and claim on the short mutable tape. -/
  position : Position

/-- A framed raw assignment followed by the encoded short position. -/
enc_structure encPrepared : Prepared where assignment : encBits, position : encPosition

/-- Read only as many low index digits as the binary precision can occupy. -/
@[expose] def cappedBit (x : Input) : ℕ :=
  ofBits (x.bit.take x.context.parameters.precision.size)

/-- The zero carry component and a bounded capped index request the product continuation. -/
@[expose] def active (x : Input) : Bool :=
  !x.carry && decide (cappedBit x < x.context.parameters.precision)

/-- Keep the assignment word and install the native balanced-product root. -/
@[expose] def prepare (claim : Bool) (x : Input) : Prepared :=
  ⟨x.path, root x.context.parameters x.context.coefficient (cappedBit x) claim⟩

/-- The three dispatch bits select the product or the claimed constant-zero answer. -/
@[expose] def instruction (claim : Bool) (x : Input) : List Bool :=
  [active x, false, !claim] ++ encPrepared (prepare claim x)

/-- On every valid traversal bit, capping removes only redundant high zeroes. -/
theorem cappedBit_eq (x : Input) (h : lsbValue x.bit < x.context.parameters.precision) :
    cappedBit x = lsbValue x.bit := by
  simpa only [cappedBit, encNat_apply, Nat.size_eq_bits_len] using
    ofBits_take_of_lt x.bit x.context.parameters.precision h

/-- Preparation retains the logical root query on every valid traversal bit. -/
theorem prepare_of_bit_lt (claim : Bool) (x : Input)
    (h : lsbValue x.bit < x.context.parameters.precision) :
    prepare claim x = ⟨x.path,
      root x.context.parameters x.context.coefficient (lsbValue x.bit) claim⟩ ∧
      active x = !x.carry := by
  simp [prepare, active, cappedBit_eq x h, h]

private structure Data where
  /-- Parameters remaining after discarding long physical words. -/
  context : Context
  /-- Low index digits, bounded by the precision's binary size. -/
  clipped : List Bool
  /-- Original component selector. -/
  carry : Bool

private enc_structure encData : Data where
  context : encContext, clipped : encBits, carry : encBool

private def data (x : Input) : Data :=
  ⟨x.context, x.bit.take x.context.parameters.precision.size, x.carry⟩

private theorem data_deg : ComputableInDegree data encInput encData 1 1 := by
  have hu : ComputableInDegree List.length encBits encUnary 1 1 :=
    ComputableInO.lengthUnary.computableInDegree DegreeBounded.self DegreeBounded.self le_rfl
  have hn : ComputableInDegree Nat.bits encNat encBits 1 1 := .of_eq fun _ => rfl
  have hs : ComputableInDegree Nat.size encNat encUnary 1 1 := by
    convert hu.comp hn using 1
    · funext n
      exact (Nat.size_eq_bits_len n).symm
    · decide
  have hp := encParameters_precision_deg.comp
    (encContext_parameters_deg.comp encInput_context_deg)
  have hclip := ComputableInDegree.bitsTake.comp (encInput_bit_deg.prod (hs.comp hp))
  exact encData_mk_deg.comp (encInput_context_deg.prod (hclip.prod encInput_carry_deg))

private theorem data_size : PolyBounded (fun x : Input => (encContext x.context).length + 1)
    (fun x => (encData (data x)).length) := by
  apply PolyBounded.of_forall_le 6 1
  intro x
  have hclip := List.length_take_le x.context.parameters.precision.size x.bit
  simp only [data, encData_apply, encDataFields, encContext_apply, encContextFields,
    encParameters_apply, encParametersFields, length_encPair, encBits_apply,
    encNat_apply, Nat.size_eq_bits_len, encBool_apply, List.length_singleton, pow_one]
  omega

private theorem compiled_poly (claim : Bool) : ComputableInPolyTime
    (fun z : Data =>
      ([!z.carry && decide (ofBits z.clipped < z.context.parameters.precision), false, !claim],
        root z.context.parameters z.context.coefficient (ofBits z.clipped) claim))
    encData (encPair encBits encPosition) := by
  have hc := encData_context_deg.computableInPolyTime
  have hp := encContext_parameters_polyTime hc
  have hb := bitsToNat.comp encData_clipped_deg.computableInPolyTime
  have hactive := bool_and' (bool_not.comp encData_carry_deg.computableInPolyTime)
    (binary_lt' hb (encParameters_precision_polyTime hp))
  have hflag : ComputableInPolyTime (fun b : Bool => [b, false, !claim]) encBool encBits :=
    of_finite _
  exact (hflag.comp hactive).prod
    (root_polyTime hp (encContext_coefficient_polyTime hc) hb (const claim))

/-- Native preparation charges every physical word linearly; only the short context occurs
inside the polynomial. The certificate holds for arbitrarily padded and malformed raw indices. -/
theorem exists_instruction_inO (claim : Bool) : ∃ d, ComputableInO (instruction claim)
    encInput encBits
    (fun x => (encInput x).length + ((encContext x.context).length + 1) ^ d)
    (fun x => (encInput x).length + ((encContext x.context).length + 1) ^ d) := by
  obtain ⟨T, S, hT, hS, hs⟩ := (compiled_poly claim).exists_computableInO
  have h := hs.comp data_deg.inO_one
  have hf := (ComputableInDegree.fst encBits encPosition).inO_one.comp_linear h
  have hp := (ComputableInDegree.snd encBits encPosition).inO_one.comp_linear h
  have hprepared := (encInput_path_deg.inO_one.prod hp).of_enc_eq
    (g := prepare claim) (encC := encPrepared) (fun _ => rfl)
  have hw := hf.append hprepared (g := instruction claim) (encOut := encBits) (fun _ => rfl)
  have hsmall : PolyBounded (fun x : Input => (encContext x.context).length + 1)
      (fun x => 2 * (T (data x) + S (data x))) :=
    (PolyBounded.const 2).mul ((hT.comp data_size).add (hS.comp data_size))
  obtain ⟨c, d, hb⟩ := hsmall.exists_le_linear_add_pow
    (fun x => (encInput x).length) 3 (fun x => by omega)
  refine ⟨d, hw.mono c (fun x => ?_) (fun x => ?_)⟩ <;>
    refine le_trans ?_ (hb x) <;>
    change (encInput x).length + _ + ((encInput x).length + ((encInput x).length + _)) ≤
      3 * (encInput x).length + 2 * (T (data x) + S (data x)) <;>
    omega

end Turing.MultiTapeATM.StoppingLeafRequest
