/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.BitMap
public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.Emit.Interpretation

/-!
# Emitting canonical configurations through an interpretation

The fixed fragment table includes the canonical configurations of quantifiers and controls.
All matrix wires start inactive. Compositional bit maps concatenate these local bit lists in
the same order as the colored instruction emitter.

## Main definitions

* `Cslib.Complexity.NCL.QBF.Emit.Interpretation.opcodeBits`: a fragment's canonical bits.
* `Cslib.Complexity.NCL.QBF.Emit.Interpretation.configurationBits`: concatenated instruction bits.

## Main results

* `Cslib.Complexity.NCL.QBF.Emit.Interpretation.configurationBits_circuit`: canonical circuit bits.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.QBF.Emit.Interpretation

open Diagram

/-- Canonical created-edge directions of a fixed fragment, including both swap color orders. -/
@[expose] def opcodeBits (B : BitMap Gate) (recorded : Bool) (op : Opcode) : List Bool :=
  B.bits op.data.diagram (op.data.orient recorded)

/-- Concatenate canonical fragment bits in edge-creation order. -/
@[expose] def configurationBits (B : BitMap Gate) (recorded : Bool) (p : Program) : List Bool :=
  p.flatMap fun i => opcodeBits B recorded i.2

variable (B : BitMap Gate)

private theorem configurationBits_layout {a b : List Color} {D : Diagram Gate a b}
    {s : D.Edge → Bool} {k : ℕ} {p : Program} {recorded : Bool} (h : Layout recorded D s k p) :
    configurationBits B recorded p = B.bits D s := by
  induction h with
  | id => exact (B.bits_id _ _).symm
  | cell => exact List.flatMap_singleton _ _
  | comp _ _ ih₁ ih₂ =>
    rw [B.bits_comp, ← ih₁, ← ih₂]
    exact List.flatMap_append
  | tensor _ _ ih₁ ih₂ =>
    rw [B.bits_tensor, ← ih₁, ← ih₂]
    exact List.flatMap_append

/-- The emitted body bits equal the canonical configuration under the bit map. -/
theorem configurationBits_body (recorded : Bool) (qs : List Quantifier) (ms : List (List Bool)) :
    configurationBits B recorded (chain 0 qs ++ terminal 0 qs.length ms) =
      B.bits (Matrix.body qs ms) (Initial.body qs ms).orient :=
  configurationBits_layout B (Layout.body qs ms)

/-- The emitted bits equal the canonical configuration of the interpreted complete circuit. -/
theorem configurationBits_circuit (recorded : Bool) (qs : List Quantifier)
    (ms : List (List Bool)) :
    configurationBits B recorded (circuit qs ms) =
      B.bits (OutputLatch.diagram.comp (Matrix.body qs ms))
        ((OutputLatch.canonical recorded true false).comp (Initial.body qs ms)).orient :=
  configurationBits_layout B (Layout.circuit recorded qs ms)

end Cslib.Complexity.NCL.QBF.Emit.Interpretation
