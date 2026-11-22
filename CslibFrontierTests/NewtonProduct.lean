/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.NewtonProduct

namespace CslibFrontierTests.NewtonProduct

open Turing Turing.MultiTapeTM Turing.MultiTapeATM
open Cslib GaloisRingArith NewtonProductRequest
open Cslib.Circuits.Frontier.FastContraction

-- The overlay passed by the signed multiplier has unchanged encoded bytes.
example (a : Input) : encInput a = SignedOperandRequest.encRequest
    ⟨encContext a.context, a.right, a.coefficient, a.bit, a.claim⟩ := encInput_eq a

-- Both product forms preserve the coordinates and select their distinct predecessor stages.
example : request ⟨⟨[true, false, true], NewtonQuery.address (.product 4)⟩,
    false, 7, 5, false⟩ = ⟨[true, false, true], 0, 7, 5, false⟩ := rfl
example : request ⟨⟨[true, false, true], NewtonQuery.address (.product 4)⟩,
    true, 7, 5, true⟩ = ⟨[true, false, true], NewtonQuery.address (.iterate 4), 7, 5, true⟩ := rfl
example : request ⟨⟨[], NewtonQuery.address (.iterate 1)⟩, false, 0, 0, false⟩ =
    ⟨[], NewtonQuery.address (.iterate 0), 0, 0, false⟩ := rfl
example : request ⟨⟨[], NewtonQuery.address (.iterate 1)⟩, true, 0, 0, true⟩ =
    ⟨[], NewtonQuery.address (.factor 0), 0, 0, true⟩ := rfl

-- This is the strict rank decrease used by the enclosing recursion.
example (node : NewtonQuery.Node) (h : NewtonQuery.operation node = 2) (right : Bool) :
    (request ⟨⟨[], NewtonQuery.address node⟩, right, 0, 0, true⟩).stage <
      NewtonQuery.address node := by
  rw [request_address]
  apply NewtonQuery.address_child_lt node _ right
  rintro rfl
  simp [NewtonQuery.operation] at h

private theorem value_child_one (m : ℕ) (right : Bool) :
    NewtonQuery.value m 1 [1] (NewtonQuery.child (.product 0) right) = 1 := by
  cases right
  · simp [NewtonQuery.child, NewtonQuery.value]
  · simp only [NewtonQuery.child, ↓reduceIte, NewtonQuery.value]
    rw [NewtonQuery.iterate_zero, residueSeed]
    have hunit : IsUnit (val 1 (modulus m) (residueCoeffs [1])) := by simp [residueCoeffs]
    rw [val_inv_of_isUnit (irreducible_modulus m) hunit]
    simp [residueCoeffs]

/-- The constant-one coefficient witness shared by the native multiplication regressions. -/
public theorem coefficient_one (m : ℕ) (i : Fin (modulus m).length) :
    ((representative m 1 (1 : Ring 1 (modulus m))).coeff i.val).val.testBit 0 =
      decide (i.val = 0) := by
  have h : (1 : Ring 1 (modulus m)) = val 1 (modulus m) [1] := by simp
  rw [h, representative, coeff_modByMonicHom_val, ite_eq_left i.isLt]
  rcases i with ⟨_ | i, hi⟩ <;> norm_num [List.getD_eq_getElem?_getD, ZMod.val_one_eq_one_mod]

-- A real native predicate answers the constant polynomial one at both predecessor stages.
private theorem exists_one_child (D : ℕ) :
    ∃ (a : ℕ) (S : Type) (_ : Finite S) (child : MultiTapeATM (a + 2) Bool S) (t : ℕ),
      ∀ (input : List Bool) (stage : Fin 2) (coefficient : Fin D) (claim : Bool),
        let req : Query := ⟨[], stage.val, coefficient.val, 0, claim⟩
        let cfg := SharedWordFork.start (Fin.natAdd a 0) child input (encQuery req) 0
        child.HaltsWithin t cfg ∧ (child.AcceptsWithin t cfg ↔ decide (coefficient.val = 0) =
          claim) := by
  classical
  have hp : ComputableInPolyTime (fun req : Query => decide (decide (req.coefficient = 0) =
      req.claim)) encQuery encBool :=
    ComputableInPolyTime.decide_eq'
      (ComputableInPolyTime.decide_eq' encQuery_coefficient_deg.computableInPolyTime
        (ComputableInPolyTime.const 0)) encQuery_claim_deg.computableInPolyTime
  obtain ⟨a, S, hS, child, c, e, hc⟩ := WorkTapePredicate.exists_alternating_of_polyTime hp
  let charge : Fin 2 × Fin D × Bool → ℕ
    | (stage, coefficient, claim) =>
        c * ((encQuery ⟨[], stage.val, coefficient.val, 0, claim⟩).length + 1) ^ e
  let t := Finset.univ.sup charge
  refine ⟨a, S, hS, child, t, ?_⟩
  intro input stage coefficient claim req cfg
  have hb := Finset.le_sup (s := (Finset.univ : Finset (Fin 2 × Fin D × Bool)))
    (f := charge) (b := (stage, coefficient, claim)) (Finset.mem_univ _)
  have he : cfg = (WorkTapePredicate.config input (encQuery req)).withState
      (some child.toPTM.initial) :=
    SharedWordFork.start_eq_workTape child input (encQuery req)
  rw [he]
  have hh := hc req input
  exact ⟨hh.2.mono hb, ⟨fun h => by simpa using hh.1.mp (h.of_halted_stepCoins hh.2),
    fun h => (hh.1.mpr (by simpa using h)).mono hb⟩⟩

-- At positive precision the actual product branch checks 1 times its residue inverse.
-- It builds its own internal layout from a request; the finite child is constructed above.
public theorem exists_one_product : ∃ (K : ℕ) (source : Fin K) (Q : Type) (_ : Finite Q)
    (atm : MultiTapeATM K Bool Q) (clock : ℕ),
    ∀ (input : List Bool) (coefficient : Fin 2) (claim : Bool),
      let a : ReducedProductRequest.Input :=
        ⟨encContext ⟨[], NewtonQuery.address (.product 0)⟩, ⟨0, 1, coefficient.val, 0, claim⟩⟩
      let cfg := SharedWordFork.start source atm input (ReducedProductRequest.encInput a) 0
      atm.HaltsWithin clock cfg ∧ (atm.AcceptsWithin clock cfg ↔
        decide (coefficient.val = 0) = claim) := by
  let q := 3 ^ modulusExp 0
  obtain ⟨a, S, hS, child, t, hc⟩ := exists_one_child (2 * q)
  let := hS
  obtain ⟨K, source, Q, hQ, atm, C, D, h⟩ :=
    NewtonProduct.exists_evaluator (Fin.natAdd a 0) child
  let cost (v : Fin 2 × Bool) := C * (0 + ((NewtonQuery.address (.product 0)).size +
    (ReducedProductRequest.encMetadata ⟨0, 1, v.1.val, 0, v.2⟩).length + 1) ^ D + 1) + t
  let clock := Finset.univ.sup cost
  refine ⟨K, source, Q, hQ, atm, clock, ?_⟩
  intro input coefficient claim req cfg
  have hi : coefficient.val < (modulus 0).length := by
    rw [length_modulus]
    have hb : 0 < 3 ^ modulusExp 0 := by positivity
    have := coefficient.isLt
    omega
  let i : Fin (modulus 0).length := ⟨coefficient.val, hi⟩
  have hs := h input [] 0 1 t [1] (.product 0) rfl i (by
    intro right coefficient bit answer
    have hstage : NewtonQuery.address (NewtonQuery.child (.product 0) right) < 2 := by
      cases right <;> decide
    have hcoef : coefficient.val < (modulus 0).length := by
      simpa only [length_modulus] using coefficient.isLt
    have hb : bit.val = 0 := by omega
    have hr := hc input ⟨_, hstage⟩ coefficient answer
    simpa only [hb, value_child_one, coefficient_one 0 ⟨coefficient.val, hcoef⟩] using hr)
    (0 : Fin 1) claim
  have hv : NewtonQuery.value 0 1 [1] (.product 0) = 1 := by
    simp only [NewtonQuery.value]
    have hz := value_child_one 0 true
    simpa only [NewtonQuery.child, ↓reduceIte, NewtonQuery.value, val_singleton,
      Nat.cast_one, one_mul] using hz
  have ha := hs.2
  simp only [Fin.val_zero] at ha
  rw [hv, coefficient_one 0 i] at ha
  have hb := Finset.le_sup (s := (Finset.univ : Finset (Fin 2 × Bool)))
    (f := cost) (b := (coefficient, claim)) (Finset.mem_univ _)
  exact ⟨hs.1.mono hb, ⟨fun h => ha.mp (h.of_halted_stepCoins hs.1),
    fun h => (ha.mpr h).mono hb⟩⟩

end CslibFrontierTests.NewtonProduct
