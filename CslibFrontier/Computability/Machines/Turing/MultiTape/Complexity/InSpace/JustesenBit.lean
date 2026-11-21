/-
Copyright (c) 2026 Christian Reitwiessner, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Justesen
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.BinaryFieldHorner
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Wozencraft

/-!
# An indexed Justesen bit from a retained field context

Decode the indexed field point, evaluate the binary label's packed coefficient blocks and
select the indicated Wozencraft bit. The workspace bound composes the certificates of these
operations and charges the retained modulus and decoded point to the encoded request.

* `Cslib.Code.JustesenFamily.fieldContext_indexedBit_eq` identifies the result with the
  existing table-free indexed bit.
* `Cslib.Code.JustesenFamily.fieldContext_indexedBit_inSpace` composes the
  native space bounds for decoding, packed Horner evaluation and bit selection.
-/

public section

namespace Cslib.Code.JustesenFamily

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInSpace
open Turing.BinaryField

private def selectBit (ctx : FieldContext) (label : ℕ) (coord : CoordinateWord) : Bool :=
  let y := (⟨ctx.modulus, coord.point, label, ctx.count⟩ : HornerInput).evaluate
  wozencraftBitWith (BinaryField.fieldMulMod ctx.modulus) coord.point y coord.half coord.bit

/-- Compute one Justesen bit from a retained field context, a binary label and a binary index. -/
def FieldContext.indexedBit (ctx : FieldContext) (label index : ℕ) : Bool :=
  selectBit ctx label (ctx.decodeWord index)

/-- At valid labels and indices, the retained-context evaluator returns the existing indexed
table-free Justesen bit. -/
theorem fieldContext_indexedBit_eq {w n : ℕ} (label : Fin w) (index : Fin (codeLength w n)) :
    (fieldContext w n).indexedBit label.val index.val = indexedCodewordMod label index := by
  unfold FieldContext.indexedBit
  rw [fieldContext_decodeWord_eq, indexedCodewordMod_eq_hornerBits]
  obtain ⟨point, half, bit⟩ := decodeCoordinate w n index
  simp only [selectBit, HornerInput.evaluate_eq]
  rw [length_fieldContext_modulus, Nat.add_sub_cancel, fieldContext_eq]

/-- Framed (retained field context, binary label), followed by the binary bit index. -/
abbrev encIndexedBitInput := encPair (encPair encFieldContext encNat) encNat

/-- The indexed bit uses workspace linear in the encoded context, label and index. -/
theorem fieldContext_indexedBit_inSpace :
    ComputableInSpace (fun ((ctx, label), index) => ctx.indexedBit label index)
      encIndexedBitInput encBool (fun p => (encIndexedBitInput p).length) := by
  let encPrepared := encPair (encPair encFieldContext encNat) encCoordinateWord
  have hmodulus : ComputableInSpace (fun word : List Bool => word) encBits encCoefficients
      (fun word => (encBits word).length) :=
    of_inO ComputableInDegree.bitsToList.inO_one
  let encOperands := encPair encCoefficients (encPair encCoefficients encCoefficients)
  have hmul :
      ComputableInSpace
        (fun p : List Bool × List Bool × List Bool => BinaryField.fieldMulMod p.1 p.2.1 p.2.2)
        encOperands encCoefficients (fun p => (encOperands p).length) := by
    have hm := fst encCoefficients (encPair encCoefficients encCoefficients)
    have hab := snd encCoefficients (encPair encCoefficients encCoefficients)
    exact budget_comp_linear fieldMulMod_inSpace (encMulInput_mk_budget hm
      (budget_comp_linear (fst encCoefficients encCoefficients) hab)
      (budget_comp_linear (snd encCoefficients encCoefficients) hab))
  have hselect :
      ComputableInSpace (fun ((ctx, label), coord) => selectBit ctx label coord)
        encPrepared encBool (fun p => (encPrepared p).length) := by
    have hctxLabel := fst (encPair encFieldContext encNat) encCoordinateWord
    have hctx := budget_comp_linear (fst encFieldContext encNat) hctxLabel
    have hlabel := budget_comp_linear (snd encFieldContext encNat) hctxLabel
    have hcoord := snd (encPair encFieldContext encNat) encCoordinateWord
    have hm := budget_comp_linear hmodulus (encFieldContext_modulus_budget hctx)
    have hx := encCoordinateWord_point_budget hcoord
    have hy := budget_comp_linear HornerInput.evaluate_inSpace
      (encHornerInput_mk_budget hm hx hlabel (encFieldContext_count_budget hctx))
    have hreq := Turing.Wozencraft.encBitInput_mk_budget encCoefficients hm hx hy
      (encCoordinateWord_half_budget hcoord) (encCoordinateWord_bit_budget hcoord)
    exact (budget_comp_linear (Turing.Wozencraft.bitWith_inSpace hmul) hreq).of_enc_eq
      fun ⟨⟨_, _⟩, _⟩ => rfl
  have hctxLabel := fst (encPair encFieldContext encNat) encNat
  have hctx := budget_comp_linear (fst encFieldContext encNat) hctxLabel
  have hindex := snd (encPair encFieldContext encNat) encNat
  have hcoord := budget_comp_linear fieldContext_decodeWord_inSpace (budget_prod hctx hindex)
  exact (budget_comp_linear hselect (budget_prod hctxLabel hcoord)).of_enc_eq
    fun ⟨⟨_, _⟩, _⟩ => rfl

end Cslib.Code.JustesenFamily
