/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: local-only (test driver)

public import
  CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.PacketSourceProduct
public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.NativeChildPolyTime

/-!
Ordinary-import tests for the fixed source-power product. They distinguish active copies,
unused copies and nonsource modes, exercise missing and oversized exponents, and apply the
product identity to the exponent slice of an actual budgeted native call.
-/

public section

namespace Turing.MultiTapeTM.PacketSourceProduct.Tests

open Cslib Cslib.Circuits.Frontier NativePacket NativeChild TensorNetwork GaloisRingArith Finset

private def packet : PacketCtx :=
  ⟨3, [1], 2, 4, 0, 2, -1, 1, true, false, true, [(1, true), (3, true)], []⟩

-- Mode zero is not a source, even if its exponent requests copies.
example : selected (ofPacket packet [3, 2] 0) = false := by decide

-- Positions three and four are the two copies of source mode one; position five is unused.
example : selected (ofPacket packet [0, 2] 3) = true := by decide
example : selected (ofPacket packet [0, 2] 4) = true := by decide
example : selected (ofPacket packet [0, 2] 5) = false := by decide

-- Missing exponent entries and positions beyond the product give identity factors.
example : selected (ofPacket packet [] 3) = false := by decide
example : selected (ofPacket packet [0, 3] 6) = false := by decide

-- The guard remains total and efficient on an oversized exponent. It clips replication to p.
example : selected (ofPacket packet [0, 2 ^ 100] 5) = true := by decide

-- The final repetition is present at exponent exactly p, rather than only below p.
example : selected (ofPacket packet [0, 3] 5) = true := by decide

-- Every guard rejects at zero precision, including at the first position.
example : selected (ofPacket { packet with p := 0 } [0, 2 ^ 100] 0) = false := by decide

-- The mode value is two, so repeating it twice gives the ring scalar four.
example : (∏ v ∈ range 6, factor packet [0, 2] v) = (4 : Ring 3 [1]) := by
  rw [show 6 = (packet.tiles * packet.nb) * packet.p from rfl,
    prod_factor_eq_sourceProduct packet [0, 2] (by simp [packet])]
  change val 3 [1] (sourceProduct packet [0, 2]) = (4 : Ring 3 [1])
  norm_num [packet, sourceProduct, sourceModes, val_prodList, modeValueList, val_sumList,
    val_pow, val_intConst, modeSources, List.range_succ]

-- Empty exponent lists have zero entries, so all powers are zero powers and the product is one.
example (c : PacketCtx) :
    (∏ v ∈ range ((c.tiles * c.nb) * c.p), factor c [] v) = 1 := by
  rw [prod_factor_eq_sourceProduct c [] (by simp), sourceProduct, val_prodList]
  simp [Function.comp_def, val_pow]

/-- Actual packet-major budget tuples supply the exponent bound for every birth slice. -/
theorem prod_birthSlice_eq_sourceProduct (fl : List ℕ) (a i pt packets group packet : ℕ)
    (t : ℤ) (ζ β : List ℕ)
    (hβ : β ∈ BudgetTuples.budgetTuples (modeWeights packets (2 ^ (i + 1)) pt) pt) :
    let c := packetCtx fl a i pt t ζ group packet
    (∏ v ∈ range ((c.tiles * c.nb) * c.p), factor c (betaSlice i pt β packet) v) =
      val pt fl (sourceProduct c (betaSlice i pt β packet)) := by
  dsimp only
  apply prod_factor_eq_sourceProduct
  intro b hb
  change b ≤ pt
  apply (BudgetTuples.lt_of_mem_budgetTuples ?_ hβ (mem_of_mem_betaSlice i pt β hb)).le
  intro w hw
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hw
  exact Nat.succ_pos _

end Turing.MultiTapeTM.PacketSourceProduct.Tests
