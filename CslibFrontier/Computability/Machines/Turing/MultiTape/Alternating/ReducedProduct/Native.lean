/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.ReducedProduct
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.SignedOperandRunner
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarrySaveSignedCorrection
import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarrySaveLeafFamily
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.WordsRoundTrip

/-!
# Native signed multiplication from a recursive operand-bit machine

The two operand routers and the five sign-correction ports share one finite physical leaf
layout. The existing streamed product evaluator then computes a coefficient bit on its prepared
root tapes. Its only continuation premise concerns the supplied finite machine on valid
coefficient-bit requests. No per-port machine or realization certificate is supplied by the caller.

The explicit preparation budget adds the two operand overheads and the correction overhead,
with the recursive child's time added once. Each operand overhead remains linear in the protected
payload. The construction of recursive operands and entry from the enclosing computation remain
parts of the complete counting simulation tracked by #4728.
-/

public section

namespace Turing.MultiTapeATM.ReducedProduct.Native

open MultiTapeTM Cslib GaloisRingArith
open Cslib.Circuits.Frontier.FastContraction
open SignedOperandRequest

private theorem transfer {k K : ℕ} {S Q : Type}
    (child : Bool → Bool → MultiTapeATM (k + 12) Bool S)
    (family : Bool → Bool → MultiTapeATM (K + 12) Bool Q)
    (input context count width : List Bool) (time total B : ℕ) (hclock : time ≤ total)
    (heq : ∀ (height bits path unary : List Bool) (frontier : ℤ) (status carry claim : Bool),
      let start := (CarrySaveLeaf.initial K input context count width height bits path unary
        frontier status).withState (some (family carry claim).toPTM.initial)
      let original := (CarrySaveLeaf.initial k input context count width height bits path unary
        frontier status).withState (some (child carry claim).toPTM.initial)
      ((family carry claim).HaltsWithin time start ↔
        (child carry claim).HaltsWithin time original) ∧
        ((family carry claim).AcceptsWithin time start ↔
          (child carry claim).AcceptsWithin time original))
    (ht : CarrySaveStream.LeafBound child time B input
      (CarrySaveLeaf.scratch k context count width)) :
    CarrySaveStream.LeafBound family total B input (CarrySaveLeaf.scratch K context count width) ∧
      ∀ {p : ℕ} (leaves : List Bool → BitString (p + p)),
        CarrySaveStream.LeafCorrect leaves child time B input
          (CarrySaveLeaf.scratch k context count width) →
        CarrySaveStream.LeafCorrect leaves family total B input
          (CarrySaveLeaf.scratch K context count width) := by
  constructor
  · intro height bits path unary frontier status carry claim hfront hsize
    exact ((heq height bits path unary frontier status carry claim).1.mpr
      (ht height bits path unary frontier status carry claim hfront hsize)).mono hclock
  · intro p leaves ha height bits path unary frontier status carry claim hfront hsize hbit
    have hh := (heq height bits path unary frontier status carry claim).1.mpr
      (ht height bits path unary frontier status carry claim hfront hsize)
    exact (show (family carry claim).AcceptsWithin total _ ↔
      (family carry claim).AcceptsWithin time _ from
        ⟨fun h => h.of_halted_stepCoins hh, fun h => h.mono hclock⟩).trans
      ((heq height bits path unary frontier status carry claim).2.trans
        (ha height bits path unary frontier status carry claim hfront hsize hbit))

/-- A finite native product evaluator on the prepared root layout. The sole child premise is
its actual halting and bit semantics on valid operand requests carrying the protected payload.
All seven local ports are constructed here, and the child time enters the product clock once. -/
theorem exists_evaluator {N : ℕ} {S : Type} [Finite S] (src : Fin N)
    (child : MultiTapeATM N Bool S) :
    ∃ (k r z : ℕ) (Q : Type) (_ : Finite Q)
      (atm : MultiTapeATM (CarryLookaheadCountingLayout.size k r z) Bool Q)
      (c e Cc dc : ℕ) (Co dO : Bool → ℕ),
      ∀ (input payload : List Bool) (m p t : ℕ) (x y : Ring p (modulus m))
        (i : Fin (modulus m).length),
        let q := 3 ^ modulusExp m
        let L := Nat.clog 2 (2 * q) + Nat.clog 2 p + 2
        let n := 2 ^ L
        let count := encNat n
        let width := encNat p
        let B := CarrySaveCountingRoot.sizeBudget n p
        let ctx : Context := ⟨payload, q, i.val⟩
        let size := q.size + i.val.size + count.length + width.length + B + 1
        let leafTime :=
          Cc * ((encContext ctx).length + count.length + width.length + (B + 2) ^ dc + 1) +
          Co false * (payload.length + size ^ dO false + 1) +
          Co true * (payload.length + size ^ dO true + 1) + t
        (∀ req : Request, req.payload = payload → req.coefficient < 2 * q → req.bit < p →
          let target := SharedWordFork.start src child input (encRequest req) 0
          child.HaltsWithin t target ∧ (child.AcceptsWithin t target ↔
            (if req.right then ((representative m p y).coeff req.coefficient).val
              else ((representative m p x).coeff req.coefficient).val).testBit req.bit =
                req.claim)) →
        ∀ (bit : Fin p) (claim : Bool),
          let cfg := (CarryLookaheadCounting.initial k r z input (encContext ctx) n p bit.val
            claim).withState (some atm.toPTM.initial)
          let clock := CarryLookaheadCounting.clockOfRoot c e p
            (40 * L + 2 * L.size + 2 * p.size + (leafTime + 10) + 1)
          atm.HaltsWithin clock cfg ∧ (atm.AcceptsWithin clock cfg ↔
            ((representative m p (x * y)).coeff i.val).val.testBit bit.val = claim) := by
  classical
  choose opK opQ opFin opLeaf Co dO hoperand using
    fun right => SignedOperandRunner.exists_leaves right src child
  let : ∀ right, Finite (opQ right) := opFin
  obtain ⟨ko, Qo, hQo, joined, hjoined⟩ := CarrySaveLeafFamily.exists_family opK opQ
    (fun right _ => opLeaf right)
  let := hQo
  obtain ⟨kc, Qc, hQc, correction, Cc, dc, hcorrection⟩ := CarrySaveSignedCorrection.exists_leaves
  let := hQc
  let sizes : Bool → ℕ
    | false => kc
    | true => ko
  let states : Bool → Type
    | false => Qc
    | true => Qo
  let : ∀ b, Finite (states b) := fun b => by cases b <;> assumption
  let merged (b : Bool) : Bool → Bool → Bool → MultiTapeATM (sizes b + 12) Bool (states b) :=
    match b with
    | false => fun _ carry claim => correction carry claim
    | true => fun side carry claim => joined side false carry claim
  obtain ⟨k, Q, hQ, all, hall⟩ := CarrySaveLeafFamily.exists_family sizes states merged
  let := hQ
  let ports (j : Fin 7) := all (decide (j = 0 ∨ j = 1)) (decide (j = 1))
  obtain ⟨r, z, R, hR, atm, c, e, hproduct⟩ := ReducedProduct.exists_evaluator ports
  refine ⟨k, r, z, R, hR, atm, c, e, Cc, dc, Co, dO, ?_⟩
  intro input payload m p t x y i q L n count width B ctx size leafTime hchild bit claim
  let a := representative m p x
  let b := representative m p y
  let operandTime (right : Bool) := Co right * (payload.length + size ^ dO right + 1) + t
  let correctionTime :=
    Cc * ((encContext ctx).length + count.length + width.length + (B + 2) ^ dc + 1)
  have routed (right : Bool) (path bits : List Bool) (carry claim : Bool)
      (hen : (ConvolutionOperand.Signed.source
        (query right ⟨ctx, count, width, path, carry, bits⟩)).isSome = true) := by
    let requestInput : Input := ⟨ctx, count, width, path, carry, bits⟩
    have hb := request_bounds right claim requestInput hen
    have hcoeff : (request right claim requestInput).coefficient < 2 * q := hb.1
    have hbit : (request right claim requestInput).bit < p := by
      simpa only [requestInput, width, ofBits_encNat] using hb.2
    exact hchild (request right claim requestInput) rfl hcoeff hbit
  have operand (right : Bool) :
      CarrySaveStream.LeafBound (opLeaf right) (operandTime right) B input
        (CarrySaveLeaf.scratch (opK right) (encContext ctx) count width) ∧
      CarrySaveStream.LeafCorrect (signedPorts a b q i.val (if right then 1 else 0))
        (opLeaf right) (operandTime right) B input
        (CarrySaveLeaf.scratch (opK right) (encContext ctx) count width) := by
    have hs := hoperand right input ctx count width B t (by
      intro path bits carry claim _
      dsimp only
      intro hen
      exact (routed right path bits carry claim hen).1)
    refine ⟨hs.1, hs.2 a b (ofBits_encNat p) ?_⟩
    intro path bits carry claim _
    dsimp only
    intro hen
    exact (routed right path bits carry claim hen).2
  have hcor := hcorrection input (encContext ctx) count width B
  have operand_le (right : Bool) : operandTime right ≤ leafTime := by
    cases right <;> dsimp only [operandTime, leafTime] <;> omega
  have correction_le : correctionTime ≤ leafTime := by dsimp [correctionTime, leafTime]; omega
  have contracts (j : Fin 7) :
      CarrySaveStream.LeafBound (ports j) leafTime B input
        (CarrySaveLeaf.scratch k (encContext ctx) count width) ∧
      CarrySaveStream.LeafCorrect (signedPorts a b q i.val j) (ports j) leafTime B input
        (CarrySaveLeaf.scratch k (encContext ctx) count width) := by
    by_cases hj : j = 0 ∨ j = 1
    · let right := decide (j = 1)
      have hport : (if right then (1 : Fin 7) else 0) = j := by
        rcases hj with rfl | rfl <;> simp [right]
      have heq (height bits path unary : List Bool) (frontier : ℤ) (status carry claim : Bool) :=
        hall true right carry claim input (encContext ctx) count width height bits path unary
          frontier status (operandTime right)
      have horig (height bits path unary : List Bool) (frontier : ℤ) (status carry claim : Bool) :=
        hjoined right false carry claim input (encContext ctx) count width height bits path unary
          frontier status (operandTime right)
      have lifted := transfer (opLeaf right) (ports j) input (encContext ctx) count width
        (operandTime right) leafTime B (operand_le right) (by
          intro height bits path unary frontier status carry claim
          have h₁ := heq height bits path unary frontier status carry claim
          have h₂ := horig height bits path unary frontier status carry claim
          simpa only [ports, hj, decide_true, right, merged, sizes, states] using
            And.intro (h₁.1.trans h₂.1) (h₁.2.trans h₂.2)) (operand right).1
      refine ⟨lifted.1, lifted.2 _ ?_⟩
      simpa only [hport] using (operand right).2
    · have heq (height bits path unary : List Bool) (frontier : ℤ) (status carry claim : Bool) :=
        hall false (decide (j = 1)) carry claim input (encContext ctx) count width
          height bits path unary frontier status correctionTime
      have lifted := transfer correction (ports j) input (encContext ctx) count width
        correctionTime leafTime B correction_le (by
          intro height bits path unary frontier status carry claim
          have hfixed := heq height bits path unary frontier status carry claim
          dsimp only [merged, sizes, states] at hfixed
          simpa only [ports, hj, decide_false] using hfixed) hcor.1
      exact ⟨lifted.1, lifted.2 _ (hcor.2 a b q i.val j
        (fun h => hj (Or.inl h)) (fun h => hj (Or.inr h)))⟩
  exact hproduct input (encContext ctx) m p leafTime x y i
    (fun j => (contracts j).1) (fun j => (contracts j).2) bit claim

end Turing.MultiTapeATM.ReducedProduct.Native
