/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.SignedOperandRequest
public import CslibFrontier.Computability.Circuit.Boolean.CarryLookahead.Query.CountingInput
public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContractionMachine
import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContraction.ResidueInverse
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryLog
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Envelope

/-!
# Native preparation of a reduced-product request

A request contains the protected recursive payload and five short fields: the binary scale,
precision, coefficient, bit and claim. The native setup derives the sparse modulus half-degree
and the number of convolution leaves itself. The long payload is copied linearly and never
enters the polynomial arithmetic budget.

`exists_setup_inO` supplies the two computations used by the physical product initializer.
-/

public section

namespace Turing.MultiTapeTM.ReducedProductRequest

open Cslib.Circuits.Frontier.FastContraction ComputableInPolyTime
open Cslib.Circuits.Boolean.CarryLookahead.Query

/-- Short binary parameters selecting one coefficient bit of a reduced product. -/
structure Metadata where
  scale : ℕ
  precision : ℕ
  coefficient : ℕ
  bit : ℕ
  claim : Bool

/-- Four framed binary naturals, followed by the claim bit. -/
enc_structure encMetadata : Metadata where
  scale : encNat, precision : encNat, coefficient : encNat, bit : encNat, claim : encBool

/-- An opaque recursive payload and the product bit to be computed. -/
structure Input where
  payload : List Bool
  metadata : Metadata

/-- A framed payload followed by the short parameter record. -/
enc_structure encInput : Input where payload : encBits, metadata : encMetadata

/-- The carry-save tree has enough leaves for every signed convolution diagonal. -/
@[expose] def depth (a : Metadata) : ℕ :=
  Nat.clog 2 (2 * 3 ^ modulusExp a.scale) + Nat.clog 2 a.precision + 2

/-- Raw counting parameters; every internal tape field is derived from this word. -/
@[expose] def parameters (a : Metadata) : CountingInput.Input :=
  ⟨2 ^ depth a, ⟨a.precision, a.bit, a.claim⟩⟩

/-- The product context records its computed half-degree and retains the caller's payload. -/
@[expose] def context (a : Input) : SignedOperandRequest.Context :=
  ⟨a.payload, 3 ^ modulusExp a.metadata.scale, a.metadata.coefficient⟩

private theorem half_polyTime :
    ComputableInPolyTime (fun a : Metadata => 3 ^ modulusExp a.scale) encMetadata encNat :=
  unary_to_binary.comp
    (ResidueInverse.half_polyTime.comp encMetadata_scale_deg.computableInPolyTime)

private theorem depth_polyTime : ComputableInPolyTime depth encMetadata encUnary := by
  exact unary_add' (unary_add' (binary_clog_two.comp (binary_mul' (const 2) half_polyTime))
    (binary_clog_two.comp encMetadata_precision_deg.computableInPolyTime)) (const 2)

/-- The complete raw parameter word is computed in polynomial time in the short input. -/
theorem parameters_polyTime :
    ComputableInPolyTime parameters encMetadata CountingInput.encInput := by
  have hn := binary_two_pow.comp depth_polyTime
  have hq : ComputableInPolyTime (fun a : Metadata =>
      (⟨a.precision, a.bit, a.claim⟩ : Initial.Input)) encMetadata Initial.encInput := by
    exact Initial.encInput_mk_polyTime encMetadata_precision_deg.computableInPolyTime
      encMetadata_bit_deg.computableInPolyTime encMetadata_claim_deg.computableInPolyTime
  exact CountingInput.encInput_mk_polyTime hn hq

private def compiled (a : Metadata) : SignedOperandRequest.Context × CountingInput.Input :=
  (⟨[], 3 ^ modulusExp a.scale, a.coefficient⟩, parameters a)

private theorem compiled_polyTime : ComputableInPolyTime compiled encMetadata
    (encPair SignedOperandRequest.encContext CountingInput.encInput) :=
  (SignedOperandRequest.encContext_mk_polyTime (const []) half_polyTime
    encMetadata_coefficient_deg.computableInPolyTime).prod parameters_polyTime

private def install (a : List Bool × SignedOperandRequest.Context) :
    SignedOperandRequest.Context := { a.2 with payload := a.1 }

private theorem install_deg : ComputableInDegree install
    (encPair encBits SignedOperandRequest.encContext) SignedOperandRequest.encContext 1 1 := by
  have hs := ComputableInDegree.snd encBits SignedOperandRequest.encContext
  exact SignedOperandRequest.encContext_mk_deg.comp
    ((ComputableInDegree.fst encBits SignedOperandRequest.encContext).prod
      ((SignedOperandRequest.encContext_half_deg.comp hs).prod
        (SignedOperandRequest.encContext_index_deg.comp hs)))

/-- The two native setup functions are linear in payload length and polynomial only in the
short metadata. Their time and workspace bounds use the same fixed degree. -/
theorem exists_setup_inO : ∃ d,
    let budget := fun a : Input => a.payload.length + ((encMetadata a.metadata).length + 1) ^ d
    ComputableInO context encInput SignedOperandRequest.encContext budget budget ∧
      ComputableInO (fun a : Input => parameters a.metadata) encInput CountingInput.encInput
        budget budget := by
  obtain ⟨T, S, hT, hS, hs⟩ := compiled_polyTime.exists_computableInO
  have h := hs.comp encInput_metadata_deg.inO_one
  have hc := (install_deg.inO_one.comp_linear
    (encInput_payload_deg.inO_one.prod h.fst')).of_enc_eq
      (g := context) (encC := SignedOperandRequest.encContext) (fun _ => rfl)
  let size := fun a : Input => (encMetadata a.metadata).length + 1
  have hm : PolyBounded size (fun a : Input => (encMetadata a.metadata).length) :=
    PolyBounded.of_forall_le 1 1 (fun _ => by
      simp only [one_mul, pow_one]
      dsimp only [size]
      omega)
  let extra := fun a : Input => 20 * size a + 4 * (T a.metadata + S a.metadata) + 20
  have he : PolyBounded size extra :=
    (((PolyBounded.const 20).mul PolyBounded.self).add
      ((PolyBounded.const 4).mul ((hT.comp hm).add (hS.comp hm)))).add (.const 20)
  obtain ⟨c, d, hd⟩ := he.exists_le_linear_add_pow (fun a => a.payload.length) 20
    (fun a => by dsimp [size]; omega)
  refine ⟨d, hc.mono c (fun a => ?_) (fun a => ?_),
    h.snd'.mono c (fun a => ?_) (fun a => ?_)⟩ <;>
    refine le_trans ?_ (hd a) <;>
    simp only [encInput_apply, encInputFields, length_encPair, encBits_apply] <;>
    dsimp only [extra, size] <;> omega

end Turing.MultiTapeTM.ReducedProductRequest
