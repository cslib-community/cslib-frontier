/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.SignedOperandRequest
public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContraction.NewtonQuery
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Envelope

/-!
# Native predecessor requests at Newton product nodes

The signed multiplier's protected payload contains the enclosing context and the binary Newton
stage. The operand side selects the predecessor stage; the coefficient, bit and claimed value
are preserved. Computing the predecessor uses only the short stage and side. The enclosing
context is copied linearly, outside the polynomial arithmetic budget.

`exists_word_inO` supplies the actual native word computation consumed by the Newton product
branch. The full recursive inversion machine remains part of #4728.
-/

public section

namespace Turing.MultiTapeTM.NewtonProductRequest

open Cslib ComputableInPolyTime Cslib.Circuits.Frontier.FastContraction

/-- The unchanged enclosing context followed by a binary Newton-stage address. -/
structure Context where
  payload : List Bool
  stage : ℕ

/-- The context is framed before the binary stage address. -/
enc_structure encContext : Context where
  payload : encBits, stage : encNat

/-- The signed multiplier's operand request with its Newton context interpreted. -/
structure Input where
  context : Context
  right : Bool
  coefficient : ℕ
  bit : ℕ
  claim : Bool

/-- Exactly the signed operand request layout, with its payload parsed as `Context`. -/
enc_structure encInput : Input where
  context : encContext, right : encBool, coefficient : encNat, bit : encNat, claim : encBool

/-- The typed overlay keeps the multiplier's operand-request words unchanged. -/
theorem encInput_eq (x : Input) : encInput x = SignedOperandRequest.encRequest
    ⟨encContext x.context, x.right, x.coefficient, x.bit, x.claim⟩ := rfl

/-- A coefficient-bit claim at one Newton stage, with an opaque enclosing context. -/
structure Query where
  payload : List Bool
  stage : ℕ
  coefficient : ℕ
  bit : ℕ
  claim : Bool

/-- The context and binary indices are framed; the singleton claim bit is last. -/
enc_structure encQuery : Query where
  payload : encBits, stage : encNat, coefficient : encNat, bit : encNat, claim : encBool

/-- Select the actual predecessor stage and retain the selected coefficient-bit claim. -/
@[expose] def request (x : Input) : Query :=
  ⟨x.context.payload, (NewtonQuery.step (x.context.stage, x.right)).2,
    x.coefficient, x.bit, x.claim⟩

/-- The always-enabled native dispatch header precedes the recursive child's input word. -/
@[expose] def word (x : Input) : List Bool := [true, false, false] ++ encQuery (request x)

/-- Only the binary stage and requested coordinates enter the polynomial budget. -/
@[expose] def shortSize (x : Input) : ℕ :=
  x.context.stage.size + x.coefficient.size + x.bit.size + 1

/-- At every represented Newton stage the native router picks its semantic predecessor. -/
theorem request_address (payload : List Bool) (node : NewtonQuery.Node) (right : Bool)
    (coefficient bit : ℕ) (claim : Bool) :
    request ⟨⟨payload, NewtonQuery.address node⟩, right, coefficient, bit, claim⟩ =
      ⟨payload, NewtonQuery.address (NewtonQuery.child node right), coefficient, bit, claim⟩ := by
  simp only [request, NewtonQuery.step_address]

private def stageInput (x : Input) : ℕ × Bool := (x.context.stage, x.right)

private theorem stageInput_deg :
    ComputableInDegree stageInput encInput (encPair encNat encBool) 1 1 :=
  (encContext_stage_deg.comp encInput_context_deg).prod encInput_right_deg

private theorem stageInput_size : PolyBounded shortSize
    (fun x => (encPair encNat encBool (stageInput x)).length) := by
  apply PolyBounded.of_forall_le 4 1
  intro x
  simp only [length_encPair, stageInput, encNat_apply, encBool_apply,
    List.length_singleton, Nat.size_eq_bits_len, shortSize, pow_one]
  omega

/-- The represented request has length linear in the opaque payload and binary metadata. -/
theorem encInput_length_le (x : Input) :
    (encInput x).length ≤ 4 * (x.context.payload.length + shortSize x + 3) := by
  simp only [encInput_apply, encInputFields, encContext_apply, encContextFields,
    length_encPair, encBits_apply, encNat_apply, encBool_apply,
    List.length_singleton, Nat.size_eq_bits_len, shortSize]
  omega

/-- One native computation emits the predecessor request in linear context length and a
polynomial of the short binary metadata, in both time and charged workspace. -/
theorem exists_word_inO : ∃ d, ComputableInO word encInput encBits
    (fun x => x.context.payload.length + shortSize x ^ d)
    (fun x => x.context.payload.length + shortSize x ^ d) := by
  obtain ⟨T, S, hT, hS, hs⟩ := NewtonQuery.computableInPolyTime_step.exists_computableInO
  have hstage := (hs.comp stageInput_deg.inO_one).snd'
  have hp := (encContext_payload_deg.comp encInput_context_deg).inO_one
  have hq := encQuery_mk_deg.inO_one.comp_linear
    (hp.prod (hstage.prod (encInput_coefficient_deg.inO_one.prod
      (encInput_bit_deg.inO_one.prod encInput_claim_deg.inO_one))))
  have hr := hq.of_enc_eq (g := request) (encC := encQuery) (fun _ => rfl)
  have hh : ComputableInDegree (fun _ : Input => [true, false, false]) encInput encBits 1 1 :=
    (ComputableInDegree.const (encMid := encBits) [true, false, false]).mono
  have hw := hh.inO_one.append hr (g := word) (encOut := encBits) (fun _ => rfl)
  let extra (x : Input) := 40 * (shortSize x + 3) + T (stageInput x) + S (stageInput x)
  have he : PolyBounded shortSize extra :=
    (((PolyBounded.const 40).mul (PolyBounded.self.add (.const 3))).add
      (hT.comp stageInput_size)).add (hS.comp stageInput_size)
  obtain ⟨c, d, hd⟩ := he.exists_le_linear_add_pow (fun x => x.context.payload.length) 40
    (fun x => by simp [shortSize])
  refine ⟨d, hw.mono c (fun x => ?_) (fun x => ?_)⟩ <;>
    refine le_trans ?_ (hd x) <;> have hl := encInput_length_le x <;>
    dsimp only [extra] <;> omega

end Turing.MultiTapeTM.NewtonProductRequest
