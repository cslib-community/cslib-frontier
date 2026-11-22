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
-- The finite child and its common clock are constructed above; no child contract is assumed.
public theorem exists_one_product : ∃ (k r z : ℕ) (Q : Type) (_ : Finite Q)
    (atm : MultiTapeATM (CarryLookaheadCountingLayout.size k r z) Bool Q) (clock : ℕ),
    ∀ (input : List Bool) (claim : Bool),
      let q := 3 ^ modulusExp 0
      let n := 2 ^ (Nat.clog 2 (2 * q) + Nat.clog 2 1 + 2)
      let payload := encContext ⟨[], NewtonQuery.address (.product 0)⟩
      let ctx : SignedOperandRequest.Context := ⟨payload, q, 0⟩
      let cfg := (CarryLookaheadCounting.initial k r z input
        (SignedOperandRequest.encContext ctx) n 1 0 claim).withState (some atm.toPTM.initial)
      atm.HaltsWithin clock cfg ∧ (atm.AcceptsWithin clock cfg ↔ true = claim) := by
  let q := 3 ^ modulusExp 0
  obtain ⟨a, S, hS, child, t, hc⟩ := exists_one_child (2 * q)
  let := hS
  obtain ⟨k, r, z, Q, hQ, atm, c, e, Cc, dc, Cr, dr, Co, dO, h⟩ :=
    NewtonProduct.exists_evaluator (Fin.natAdd a 0) child
  let i : Fin (modulus 0).length := ⟨0, by rw [length_modulus]; positivity⟩
  let L := Nat.clog 2 (2 * q) + Nat.clog 2 1 + 2
  let n := 2 ^ L
  let count := encNat n
  let width := encNat 1
  let B := CarrySaveCountingRoot.sizeBudget n 1
  let payload := encContext ⟨[], NewtonQuery.address (.product 0)⟩
  let ctx : SignedOperandRequest.Context := ⟨payload, q, 0⟩
  let size := q.size + (0 : ℕ).size + count.length + width.length + B + 1
  let routeSize := (NewtonQuery.address (.product 0)).size + (2 * q).size + (1 : ℕ).size + 1
  let leafTime :=
    Cc * ((SignedOperandRequest.encContext ctx).length + count.length + width.length +
      (B + 2) ^ dc + 1) +
    Co false * (payload.length + size ^ dO false + 1) +
    Co true * (payload.length + size ^ dO true + 1) + (Cr * (0 + routeSize ^ dr + 1) + t)
  let clock := CarryLookaheadCounting.clockOfRoot c e 1
    (40 * L + 2 * L.size + 2 * (1 : ℕ).size + (leafTime + 10) + 1)
  refine ⟨k, r, z, Q, hQ, atm, clock, ?_⟩
  intro input claim q' n' payload' ctx' cfg
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
  refine ⟨hs.1, hs.2.trans ?_⟩
  have hv : NewtonQuery.value 0 1 [1] (.product 0) = 1 := by
    simp only [NewtonQuery.value]
    have hz := value_child_one 0 true
    simpa only [NewtonQuery.child, ↓reduceIte, NewtonQuery.value, val_singleton,
      Nat.cast_one, one_mul] using hz
  rw [hv]
  change ((representative 0 1 (1 : Ring 1 (modulus 0))).coeff i.val).val.testBit 0 = claim ↔
    true = claim
  rw [coefficient_one 0 i]
  rfl

end CslibFrontierTests.NewtonProduct
