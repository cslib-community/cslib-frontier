/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContraction.SignedRouting
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarrySaveWordSum
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarrySaveGate

/-!
# One physical query of a coefficient bit of contraction-ring multiplication

The two signed-diagonal selector bits precede the existing row and shift path. The leaf gate
calls one of its native operand or sign continuations. The general carry-save and lookahead
controllers are paid once over the entire reduction.
-/

public section
namespace Turing.MultiTapeATM.ReducedProduct

open MultiTapeTM Cslib GaloisRingArith Cslib.Circuits.Boolean CarrySaveQuery
open Cslib.Circuits.Frontier.FastContraction

/-- A native evaluator on the prepared word-sum layout. Its genuine child inputs are single
addressed operand bits, and its remaining ports use the binary sign predicate. The leaf
clock has coefficient one, independent of degree, precision and recursive continuation. -/
theorem exists_evaluator {k : ℕ} {S : Type} [Finite S]
    (child : Fin 7 → Bool → Bool → MultiTapeATM (k + 12) Bool S) :
    ∃ (r z : ℕ) (Q : Type) (_ : Finite Q)
      (atm : MultiTapeATM (CarryLookaheadCountingLayout.size k r z) Bool Q) (c e : ℕ),
      ∀ (input context : List Bool) (m p time : ℕ) (x y : Ring p (modulus m))
        (i : Fin (modulus m).length),
        let q := 3 ^ modulusExp m
        let L := Nat.clog 2 (2 * q) + Nat.clog 2 p + 2
        let n := 2 ^ L
        let budget := CarrySaveCountingRoot.sizeBudget n p
        let scratch := CarrySaveLeaf.scratch k context (encNat n) (encNat p)
        let a := representative m p x
        let b := representative m p y
        (∀ j, CarrySaveStream.LeafBound (child j) time budget input scratch) →
        (∀ j, CarrySaveStream.LeafCorrect (signedPorts a b q i.val j)
          (child j) time budget input scratch) →
        ∀ (bit : Fin p) (claim : Bool),
          let cfg := (CarryLookaheadCounting.initial k r z input context n p bit.val
            claim).withState (some atm.toPTM.initial)
          let clock := CarryLookaheadCounting.clockOfRoot c e p
            (40 * L + 2 * L.size + 2 * p.size + (time + 10) + 1)
          atm.HaltsWithin clock cfg ∧ (atm.AcceptsWithin clock cfg ↔
            ((representative m p (x * y)).coeff i.val).val.testBit bit.val = claim) := by
  classical
  let := Fintype.ofFinite S
  obtain ⟨r, z, Q, fin, atm, c, e, h⟩ :=
    CarrySaveWordSum.exists_finisher (CarrySaveGate.machine signedGate child)
  refine ⟨r, z, Q, fin, atm, c, e, ?_⟩
  intro input context m p time x y i q L n budget scratch a b ht ha bit claim
  have hv : b.natDegree < 2 * q := by
    simpa only [b, q, length_modulus] using natDegree_representative_lt m p y
  have hf := h input context L p (time + 10) (reducedLeaves q i.val a b)
    (CarrySaveGate.bound _ _ ht)
    (CarrySaveGate.correct _ _ (signedPorts a b q i.val) _
      (value_reduced_eq_gate a b q i.val hv) ha) bit claim
  exact ⟨hf.1, hf.2.trans (by rw [bit_reducedTree m p x y i bit])⟩

end Turing.MultiTapeATM.ReducedProduct
