/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

import CslibFrontier.Computability.PolyTime.SeededPacketPlacement
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NormalForm

open Cslib Turing Turing.MultiTapeTM SeededPacketPlacement

-- A linear seed with one label digit hashes the keys 5 and 1 to different digits.
-- Rank 1 reverses their order in the packet and the row's larger digit selects slot 1.
private def linear : Input := ⟨⟨32, 1, 0, 1, 0, 0, 0, 0⟩, 5, 1, 1⟩

private theorem linear_spec : run linear = (321, 1) := by
  simp only [run, SeededPacketPlacement.code, linear, TrinomialArithmetic.runSelected,
    TrinomialArithmetic.hash4, TrinomialArithmetic.eval4, TrinomialArithmetic.mul,
    TrinomialArithmetic.reduce, clmul_eq_foldr_bits, Probability.trinomialStep,
    Probability.trinomialTargetBits, Probability.trinomialStepAux_eq_findGreatest]
  decide

-- The same finite machine handles positive-label placement and every zero-width label pair.
example : ∃ (c d k : ℕ) (Q : Type) (_ : Finite Q) (tm : MultiTapeTM k Bool Q),
    ∀ (p : Input) (answer : ℕ × ℕ), (p = linear ∧ answer = (321, 1)) ∨
        (p.context.labelLength = 0 ∧ answer = (p.rank, 0)) →
      let budget := c * ((encInput p).length + 1) ^ d
      tm.ComputesTidilyInTimeAndSpace (encInput p) ((encPair encNat encNat) answer)
        budget budget := by
  obtain ⟨c, d, k, Q, hQ, tm, htm⟩ := Internal.NormalForm.polyTime computableInPolyTime_run
  refine ⟨c, d, k, Q, hQ, tm, fun p answer h => ?_⟩
  rcases h with ⟨rfl, rfl⟩ | ⟨hw, rfl⟩
  · simpa only [linear_spec] using htm linear
  · have hv : run p = (p.rank, 0) := by
      simp [run, SeededPacketLocation.run, PacketPacking.packetOf, PacketPacking.slotOf, hw]
    simpa only [hv] using htm p
