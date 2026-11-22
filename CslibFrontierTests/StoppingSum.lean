/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module

import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.StoppingSum

/-!
The raw-request sum compiler is specialized to the original described-network contraction.
The finite machine and all constants precede every runtime network, assignment depth,
coefficient and bit. Only the native entry-terminal contract remains supplied; no carry-save
leaf machine, product machine, circuit decoder or arithmetic routing certificate is assumed.
-/

namespace CslibFrontierTests.StoppingSum

open Turing Turing.MultiTapeTM Turing.MultiTapeATM Cslib Cslib.BitString GaloisRingArith
open Cslib.Circuits.Frontier Cslib.Circuits.Frontier.FastContraction
open StoppingQuery.ProductRouting StoppingLeafRequest

example {T S : Type} {N : ℕ} [Finite S] (assignment query : Fin N)
    (hne : assignment ≠ query) (terminal : MultiTapeATM N Bool S) :
    ∃ (K : ℕ) (source : Fin K) (Q : Type) (_ : Finite Q)
      (atm : MultiTapeATM K Bool Q) (C D P E : ℕ),
      ∀ (input : List Bool) (m p : ℕ) (d : DescribedNetwork T)
        (eval : T → List Bool → Ring p (modulus m)) (terminalTime : ℕ),
        (∀ (path : List Bool),
          path.length ≤ CarrySaveCountingRoot.sizeBudget (2 ^ d.numEdges) p → ∀ position,
          Valid ⟨m, p, d.vertices.length⟩ (2 ^ Nat.clog 2 d.vertices.length)
            (Nat.clog 2 d.vertices.length) position → player position = none →
          let cfg := (TwoWordInput.ready assignment query input path
            (encPosition position)).withState (some terminal.toPTM.initial)
          terminal.HaltsWithin terminalTime cfg ∧
            (terminal.AcceptsWithin terminalTime cfg ↔
              StoppingQuery.value m p 0 d.vertices.length
                (fun _ v => StoppingQuery.networkEntry d eval (binaryValue path) v)
                  (address position) = position.claim)) →
        ∀ (coefficient : Fin (modulus m).length) (bit : Fin p) (claim : Bool),
          let parameters : StoppingQuery.Product.Parameters := ⟨m, p, d.vertices.length⟩
          let ctx : Context := ⟨parameters, coefficient.val⟩
          let request : CarrySaveWordSum.Request :=
            ⟨encContext ctx, d.numEdges, ⟨p, bit.val, claim⟩⟩
          let start := SharedWordFork.start source atm input (CarrySaveWordSum.encRequest request) 0
          let time := C * (d.numEdges +
            ((encContext ctx).length + d.numEdges.size + p.size + 1) ^ D + 1) +
              StoppingProduct.clock P E parameters terminalTime
          atm.HaltsWithin time start ∧ (atm.AcceptsWithin time start ↔
            ((representative m p (d.contraction eval)).coeff coefficient.val).val.testBit
              bit.val = claim) := by
  obtain ⟨K, source, Q, hQ, atm, C, D, P, E, h⟩ :=
    StoppingSum.exists_evaluator assignment query hne terminal
  refine ⟨K, source, Q, hQ, atm, C, D, P, E, ?_⟩
  intro input m p d eval terminalTime hterminal coefficient bit claim
    parameters ctx request start time
  have hs := h input d.numEdges parameters (StoppingQuery.networkEntry d eval) terminalTime
    hterminal coefficient bit claim
  refine ⟨hs.1, hs.2.trans ?_⟩
  rw [StoppingQuery.sum_prod_networkEntry]

end CslibFrontierTests.StoppingSum
