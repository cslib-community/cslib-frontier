/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.ReducedProduct.Native
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.WorkTapePredicate

namespace CslibFrontierTests.NativeReducedProduct

open Turing Turing.MultiTapeTM Turing.MultiTapeATM
open Cslib SignedOperandRequest
open Cslib.Circuits.Frontier.FastContraction

-- A real native predicate answers zero operands, with one clock over all bounded requests.
private theorem exists_zero_child (D p : ℕ) :
    ∃ (k : ℕ) (S : Type) (_ : Finite S) (child : MultiTapeATM (k + 2) Bool S) (time : ℕ),
      ∀ (input : List Bool) (right : Bool) (coefficient : Fin D) (bit : Fin p) (claim : Bool),
        let req : Request := ⟨[], right, coefficient.val, bit.val, claim⟩
        let cfg := SharedWordFork.start (Fin.natAdd k 0) child input (encRequest req) 0
        child.HaltsWithin time cfg ∧ (child.AcceptsWithin time cfg ↔ false = claim) := by
  classical
  have hp : ComputableInPolyTime (fun req : Request => !req.claim) encRequest encBool :=
    ComputableInPolyTime.bool_not.comp encRequest_claim_deg.computableInPolyTime
  obtain ⟨k, S, hS, child, c, e, hchild⟩ := WorkTapePredicate.exists_alternating_of_polyTime hp
  let charge : Bool × Fin D × Fin p × Bool → ℕ
    | (right, coefficient, bit, claim) =>
        c * ((encRequest ⟨[], right, coefficient.val, bit.val, claim⟩).length + 1) ^ e
  let time := Finset.univ.sup charge
  refine ⟨k, S, hS, child, time, ?_⟩
  intro input right coefficient bit claim req cfg
  have hb := Finset.le_sup (s := (Finset.univ : Finset (Bool × Fin D × Fin p × Bool)))
    (f := charge) (b := (right, coefficient, bit, claim)) (Finset.mem_univ _)
  have hh : child.HaltsWithin (charge (right, coefficient, bit, claim)) cfg := by
    dsimp only [cfg]
    rw [SharedWordFork.start_eq_workTape]
    exact (hchild req input).2
  have ha : child.AcceptsWithin (charge (right, coefficient, bit, claim)) cfg ↔ false = claim := by
    dsimp only [cfg]
    rw [SharedWordFork.start_eq_workTape]
    refine (hchild req input).1.trans ?_
    change (!claim) = true ↔ false = claim
    cases claim <;> decide
  exact ⟨hh.mono hb, ⟨fun h => ha.mp (h.of_halted_stepCoins hh), fun h => (ha.mpr h).mono hb⟩⟩

-- The assembled product machine computes zero times zero at positive precision. The child is
-- an actual finite native predicate, and the prepared root has a valid coefficient and bit.
example : ∃ (k r z : ℕ) (Q : Type) (_ : Finite Q)
    (atm : MultiTapeATM (CarryLookaheadCountingLayout.size k r z) Bool Q) (clock : ℕ),
    ∀ (input : List Bool) (claim : Bool),
      let q := 3 ^ modulusExp 0
      let n := 2 ^ (Nat.clog 2 (2 * q) + Nat.clog 2 1 + 2)
      let ctx : Context := ⟨[], q, 0⟩
      let cfg := (CarryLookaheadCounting.initial k r z input (encContext ctx) n 1 0
        claim).withState (some atm.toPTM.initial)
      atm.HaltsWithin clock cfg ∧ (atm.AcceptsWithin clock cfg ↔ false = claim) := by
  let q := 3 ^ modulusExp 0
  obtain ⟨a, S, hS, child, t, hchild⟩ := exists_zero_child (2 * q) 1
  let := hS
  obtain ⟨k, r, z, Q, hQ, atm, c, e, Cc, dc, Co, dO, h⟩ :=
    ReducedProduct.Native.exists_evaluator (Fin.natAdd a 0) child
  let i : Fin (modulus 0).length := ⟨0, by rw [length_modulus]; positivity⟩
  let L := Nat.clog 2 (2 * q) + Nat.clog 2 1 + 2
  let n := 2 ^ L
  let count := encNat n
  let width := encNat 1
  let B := CarrySaveCountingRoot.sizeBudget n 1
  let ctx : Context := ⟨[], q, 0⟩
  let size := q.size + (0 : ℕ).size + count.length + width.length + B + 1
  let leafTime :=
    Cc * ((encContext ctx).length + count.length + width.length + (B + 2) ^ dc + 1) +
    Co false * (([] : List Bool).length + size ^ dO false + 1) +
    Co true * (([] : List Bool).length + size ^ dO true + 1) + t
  let clock := CarryLookaheadCounting.clockOfRoot c e 1
    (40 * L + 2 * L.size + 2 * (1 : ℕ).size + (leafTime + 10) + 1)
  refine ⟨k, r, z, Q, hQ, atm, clock, ?_⟩
  intro input claim q' n' ctx' cfg
  have hs := h input [] 0 1 t 0 0 i (by
    intro req hpayload hcoeff hbit
    rcases req with ⟨payload, right, coefficient, bit, answer⟩
    cases hpayload
    have hr := hchild input right ⟨coefficient, hcoeff⟩ ⟨bit, hbit⟩ answer
    refine ⟨hr.1, hr.2.trans ?_⟩
    simp [representative]) (0 : Fin 1) claim
  refine ⟨hs.1, hs.2.trans ?_⟩
  simp [representative]

end CslibFrontierTests.NativeReducedProduct
