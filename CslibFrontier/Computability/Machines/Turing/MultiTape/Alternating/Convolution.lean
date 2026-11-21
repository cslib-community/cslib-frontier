/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContraction.SparseProductQuery
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarrySaveWordSum
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarrySaveGate

/-!
# A physical modular convolution evaluator with operand continuations

One path through the coefficient tree selects a diagonal row, a multiplication shift, and one
side of their conjunction. The fixed evaluator pays its selected operand continuation once.
-/

public section
namespace Turing.MultiTapeATM.Convolution

open MultiTapeTM Cslib Cslib.BitString Cslib.Circuits.Boolean CarrySaveQuery
open Cslib.Circuits.Frontier.FastContraction

private def gate (v : Fin 7 → Bool) : Bool := v 0 && v 1

private def side (j : Fin 7) : Bool := decide (j ≠ 0)

/-- A fixed finite machine verifies a convolution bit using one charged continuation for an
operand bit on every branch. Its input configurations and scratch are the native word-sum
layout. Both the coefficient and bit widths may vary for this one machine. -/
theorem exists_evaluator {k : ℕ} {S : Type} [Finite S]
    (child : Bool → Bool → Bool → MultiTapeATM (k + 12) Bool S) :
    ∃ (r q : ℕ) (Q : Type) (_ : Finite Q)
      (atm : MultiTapeATM (CarryLookaheadCountingLayout.size k r q) Bool Q) (c e : ℕ),
      ∀ (input context : List Bool) (d p diagonal time : ℕ) (u v : Polynomial (ZMod (2 ^ p))),
        u.natDegree < d → v.natDegree < d →
        let L := Nat.clog 2 d + Nat.clog 2 p
        let n := 2 ^ L
        let budget := CarrySaveCountingRoot.sizeBudget n p
        let scratch := CarrySaveLeaf.scratch k context (encNat n) (encNat p)
        (∀ s, CarrySaveStream.LeafBound (child s) time budget input scratch) →
        (∀ s, CarrySaveStream.LeafCorrect (operandLeaves u v d diagonal s)
          (child s) time budget input scratch) →
        ∀ (bit : Fin p) (claim : Bool),
          let cfg := (CarryLookaheadCounting.initial k r q input context n p bit.val
            claim).withState (some atm.toPTM.initial)
          let clock := CarryLookaheadCounting.clockOfRoot c e p
            (40 * L + 2 * L.size + 2 * p.size + (time + 10) + 1)
          atm.HaltsWithin clock cfg ∧ (atm.AcceptsWithin clock cfg ↔
            ((u * v).coeff diagonal).val.testBit bit.val = claim) := by
  classical
  let := Fintype.ofFinite S
  obtain ⟨r, q, Q, fin, atm, c, e, h⟩ := CarrySaveWordSum.exists_finisher
    (CarrySaveGate.machine gate (fun j => child (side j)))
  refine ⟨r, q, Q, fin, atm, c, e, ?_⟩
  intro input context d p diagonal time u v hu hv L n budget scratch ht ha bit claim
  have hf := h input context L p (time + 10)
    (InnerProduct.flatLeaves (fun j : Fin d => coeffWord u j.val)
      (fun j : Fin d => diagonalWord v diagonal j.val))
    (CarrySaveGate.bound _ _ fun j => ht (side j))
    (CarrySaveGate.correct _ _ (fun j => operandLeaves u v d diagonal (side j)) _
      (fun path carry i => value_flat_eq_and u v hv diagonal path carry i)
      (fun j => ha (side j))) bit claim
  have he : (InnerProduct.result (fun j : Fin d => coeffWord u j.val)
      (fun j : Fin d => diagonalWord v diagonal j.val)) bit =
      ((u * v).coeff diagonal).val.testBit bit.val := by
    have hz := (streamedCoeff_eq d p diagonal u v).trans
      (convolutionCircuit_eq_coeff d p diagonal u v hu)
    have hv' := congrArg ZMod.val hz
    simp only [streamedCoeff, ZMod.val_natCast, Nat.mod_eq_of_lt (equivFin _ _).isLt] at hv'
    exact (testBit_equivFin _ bit).symm.trans (congrArg (fun n : ℕ => n.testBit bit.val) hv')
  have hword :
      (carryLookaheadAdd p).eval interpretation
        (tree (InnerProduct.flatLeaves (fun j : Fin d => coeffWord u j.val)
          (fun j : Fin d => diagonalWord v diagonal j.val)) L []) =
      InnerProduct.result (fun j : Fin d => coeffWord u j.val)
        (fun j : Fin d => diagonalWord v diagonal j.val) :=
    (equivFin p).injective (Fin.ext (InnerProduct.val_flat _ _))
  exact ⟨hf.1, hf.2.trans (by rw [hword, he])⟩

end Turing.MultiTapeATM.Convolution
