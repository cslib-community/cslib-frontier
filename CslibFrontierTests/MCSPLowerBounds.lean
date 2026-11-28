/-
Copyright (c) 2026 Uladzislau Artsemyeu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uladzislau Artsemyeu
-/

module
-- upstream: local-only (tests for quadratic MCSP lower bounds and communication cuts)

import CslibFrontier.Computability.MCSP.Restrictions
import CslibFrontier.Computability.MCSP.CommunicationCut

/-!
# Tests for quadratic MCSP lower bounds and communication cuts

Module-encapsulated client tests exercising `mcspSquare`, `CornerCertificates`, `card_mask_side`,
`crossingWires`, and the finite bounds at arities `16` and `32`.
-/

set_option linter.privateModule false

namespace Cslib.MCSP.Tests.MCSPLowerBounds

open Cslib.Circuits Cslib.Circuits.Boolean Cslib.Communication
open Cslib.MCSP.Restrictions Cslib.MCSP.CommunicationCut

/-! ### Quadratic MCSP slice behavior and finite lower bound -/

example : mcspSquare 1 (fun _ => true) = true :=
  mcspSquare_constant_table 1 (by decide) true

example : mcspSquare 1 (fun i => i == 1) = true := by
  rw [mcspSquare_eq_true_iff]
  let c : Circuit signature 1 1 := ⟨.empty, fun _ => Wire.input 0⟩
  have hc : c.Computes interpretation
      (single ((MCSP.truthTable 1).symm (fun i => i == 1))) := by
    intro x
    funext o
    have hx : x = fun _ => x 0 := funext fun i => congrArg x (Fin.eq_zero i)
    have h0 : x 0 = ((BitString.equivFin 1 x == 1) : Bool) := by
      rw [hx]
      cases x 0 <;> decide
    simpa [c, Circuit.eval, single, MCSP.truthTable] using h0
  exact (complexity_le_of_computes c hc).trans (by simp [c])

example : descriptionBitBound 16 = 5397 := by
  decide

example (c : Circuit signature (2 ^ 16) 1)
    (hc : c.Computes interpretation (single (mcspSquare 16))) : 120277 ≤ c.size :=
  le_size_of_le_complexity mcspSquare_sixteen_lower_bound hc

/-! ### Concrete two-corner certificate behavior -/

private def sampleCertProg : Program signature 2 2 :=
  ((Program.empty : Program signature 2 0).gate
      ⟨Boolean.Op.and, fun i => if i = 0 then Wire.input 0 else Wire.input 1⟩).gate
    ⟨Boolean.Op.or, fun i => if i = 0 then Wire.gate ⟨0, by decide⟩ else Wire.input 0⟩

example : CornerCertificates.selectedPins Boolean.Op.and (fun _ => false) = {0} := by
  decide

example :
    (CornerCertificates.cornerInputs sampleCertProg (.gate ⟨1, by decide⟩) false).card +
      (CornerCertificates.cornerInputs sampleCertProg (.gate ⟨1, by decide⟩) true).card ≤ 3 :=
  CornerCertificates.card_cornerInputs_le sampleCertProg (.gate ⟨1, by decide⟩)

example (x : BitString 2)
    (agree : ∀ i ∈ CornerCertificates.cornerInputs sampleCertProg (.gate ⟨1, by decide⟩) true,
      x i = true) :
    sampleCertProg.trace interpretation x (.gate ⟨1, by decide⟩) = true := by
  refine CornerCertificates.agrees_on_cornerInputs sampleCertProg (.gate ⟨1, by decide⟩) true ?_
    x agree
  decide

/-! ### Concrete crossing wires, balanced mask sides, and equality cuts -/

private def andGateProg : Program signature 2 1 :=
  (Program.empty : Program signature 2 0).gate
    ⟨Boolean.Op.and, fun i => if i = 0 then Wire.input 0 else Wire.input 1⟩

private def andOwner : Wire 2 1 → Bool
  | .input 0 => true
  | .input 1 => false
  | .gate 0 => true

example : Wire.input 1 ∈ crossingWires andGateProg andOwner := by
  rw [mem_crossingWires]
  decide

example : Wire.input 0 ∉ crossingWires andGateProg andOwner := by
  rw [mem_crossingWires]
  decide

example : (crossingWires andGateProg andOwner).card = 1 := by
  have hEq : crossingWires andGateProg andOwner = {Wire.input 1} := by
    ext w
    rw [mem_crossingWires, Finset.mem_singleton]
    revert w
    decide
  rw [hEq, Finset.card_singleton]

example (h : BooleanFunction 1) :
    ((Finset.univ : Finset (Fin (2 ^ (1 + (1 + 1))))).filter
      (fun i => mask 1 h i = true)).card = 4 :=
  card_mask_side h true

example :
    ∃ h : BooleanFunction 22,
      ∀ p : Protocol (BooleanFunction 9) (BooleanFunction 9) Bool,
        p.run = mixedTest h → 513 ≤ p.depth := by
  obtain ⟨h, hEq⟩ := mcspSquare_32_equality_cut
  exact ⟨h, fun p hp => protocol_depth_lower_bound h hEq p hp⟩

end Cslib.MCSP.Tests.MCSPLowerBounds
