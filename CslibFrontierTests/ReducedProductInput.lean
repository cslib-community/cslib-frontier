/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.ReducedProduct.Input
import CslibFrontierTests.NewtonProduct

namespace CslibFrontierTests.ReducedProductInput

open Turing Turing.MultiTapeTM Turing.MultiTapeATM
open Cslib GaloisRingArith ReducedProductRequest
open Cslib.Circuits.Frontier.FastContraction
open CslibFrontierTests.NewtonProduct (coefficient_one)

-- The sole external word is a framed request followed by the unframed original source.
example (payload input : List Bool) (m p coefficient bit : ℕ) (claim : Bool) :
    encPair ReducedProductRequest.encInput encBits
      (⟨payload, ⟨m, p, coefficient, bit, claim⟩⟩, input) =
      frame (frame payload ++ frame (encNat m) ++ frame (encNat p) ++
        frame (encNat coefficient) ++ frame (encNat bit) ++ [claim]) ++ input := by
  simp [encInput_apply, encInputFields, encMetadata_apply, encMetadataFields,
    encPair_apply, encBits_apply, encBool_apply, List.append_assoc]

-- Initialization remains defined across zero precision; only positive precision has bit queries.
example : parameters ⟨0, 0, 0, 0, false⟩ = ⟨32, ⟨0, 0, false⟩⟩ := rfl
example : parameters ⟨0, 1, 0, 0, true⟩ = ⟨32, ⟨1, 0, true⟩⟩ := rfl
example : parameters ⟨0, 2, 1, 1, false⟩ = ⟨64, ⟨2, 1, false⟩⟩ := rfl
example : (context ⟨[true, false, true], ⟨0, 1, 1, 0, false⟩⟩).payload =
    [true, false, true] := rfl

-- The actual finite child checks the protected payload and then the constant-one operand bit.
private theorem exists_one_child (payload : List Bool) (D : ℕ) :
    ∃ (a : ℕ) (S : Type) (_ : Finite S) (child : MultiTapeATM (a + 2) Bool S) (t : ℕ),
      ∀ (input : List Bool) (right : Bool) (coefficient : Fin D) (claim : Bool),
        let req : SignedOperandRequest.Request := ⟨payload, right, coefficient.val, 0, claim⟩
        let cfg := SharedWordFork.start (Fin.natAdd a 0) child input
          (SignedOperandRequest.encRequest req) 0
        child.HaltsWithin t cfg ∧ (child.AcceptsWithin t cfg ↔
          decide (coefficient.val = 0) = claim) := by
  classical
  have hp : ComputableInPolyTime (fun req : SignedOperandRequest.Request =>
      decide (req.payload = payload) && decide (decide (req.coefficient = 0) = req.claim))
      SignedOperandRequest.encRequest encBool :=
    ComputableInPolyTime.bool_and'
      (ComputableInPolyTime.decide_eq'
        SignedOperandRequest.encRequest_payload_deg.computableInPolyTime
        (ComputableInPolyTime.const payload))
      (ComputableInPolyTime.decide_eq'
        (ComputableInPolyTime.decide_eq'
          SignedOperandRequest.encRequest_coefficient_deg.computableInPolyTime
          (ComputableInPolyTime.const 0))
        SignedOperandRequest.encRequest_claim_deg.computableInPolyTime)
  obtain ⟨a, S, hS, child, c, e, hc⟩ := WorkTapePredicate.exists_alternating_of_polyTime hp
  let charge : Bool × Fin D × Bool → ℕ
    | (right, coefficient, claim) =>
        c * ((SignedOperandRequest.encRequest
          ⟨payload, right, coefficient.val, 0, claim⟩).length + 1) ^ e
  let t := Finset.univ.sup charge
  refine ⟨a, S, hS, child, t, ?_⟩
  intro input right coefficient claim req cfg
  have hb := Finset.le_sup (s := (Finset.univ : Finset (Bool × Fin D × Bool)))
    (f := charge) (b := (right, coefficient, claim)) (Finset.mem_univ _)
  dsimp only [cfg]
  rw [SharedWordFork.start_eq_workTape]
  have hh := hc req input
  exact ⟨hh.2.mono hb, ⟨fun h => by simpa [req] using hh.1.mp (h.of_halted_stepCoins hh.2),
    fun h => (hh.1.mpr (by simpa [req] using h)).mono hb⟩⟩

/-- A complete ordinary-input product run with a nonempty protected payload, an arbitrary
original source word and an actual finite operand child. Coefficients zero and one exercise
both truth values of the positive-precision output, for both requested claims. -/
public theorem exists_from_external_input :
    ∃ (K : ℕ) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM K Bool Q) (C D t : ℕ),
      ∀ (input : List Bool) (coefficient : Fin 2) (claim : Bool),
        let a : ReducedProductRequest.Input :=
          ⟨[true, false, true], ⟨0, 1, coefficient.val, 0, claim⟩⟩
        let word := encPair ReducedProductRequest.encInput encBits (a, input)
        let cfg := atm.toPTM.toNTM.initCfg word
        let time := C * (input.length + 3 + ((encMetadata a.metadata).length + 1) ^ D + 1) + t
        atm.HaltsWithin time cfg ∧
          (atm.AcceptsWithin time cfg ↔ decide (coefficient.val = 0) = claim) := by
  let q := 3 ^ modulusExp 0
  obtain ⟨a, S, hS, child, t, hc⟩ := exists_one_child [true, false, true] (2 * q)
  let := hS
  obtain ⟨K, Q, hQ, atm, C, D, h⟩ :=
    ReducedProduct.Input.exists_from_input (Fin.natAdd a 0) child
  refine ⟨K, Q, hQ, atm, C, D, t, ?_⟩
  intro input coefficient claim req word cfg time
  have hdegree : 2 ≤ (modulus 0).length := by
    rw [length_modulus]
    have : 0 < 3 ^ modulusExp 0 := by positivity
    omega
  let i : Fin (modulus 0).length := ⟨coefficient.val, coefficient.isLt.trans_le hdegree⟩
  have hs := h input [true, false, true] 0 1 t 1 1 i (by
    intro req hpayload hcoefficient hbit
    rcases req with ⟨payload, right, coefficient, bit, answer⟩
    dsimp only at hpayload hcoefficient hbit
    subst payload
    have hb : bit = 0 := by omega
    subst bit
    have hcoef : coefficient < (modulus 0).length := by
      simpa only [length_modulus] using hcoefficient
    have hr := hc input right ⟨coefficient, hcoefficient⟩ answer
    refine ⟨hr.1, hr.2.trans ?_⟩
    simp only [ite_self, coefficient_one 0 ⟨coefficient, hcoef⟩]) (0 : Fin 1) claim
  refine ⟨hs.1, hs.2.trans ?_⟩
  change ((representative 0 1 (1 * 1 : Ring 1 (modulus 0))).coeff i.val).val.testBit 0 = claim ↔ _
  rw [mul_one, coefficient_one]

end CslibFrontierTests.ReducedProductInput
