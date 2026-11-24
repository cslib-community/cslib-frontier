/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Embedding.PolyTime.Fragments
public import CslibFrontier.Computability.Complexity.Problems.NCL.Encoding
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# An explicit adjacent-swap routing program

For each requested incidence, retain the original wires not previously requested and move that
incidence left across its remaining predecessors. Each emitted instruction retains both wires'
colors and original directions. Prefix filtering gives a total list algorithm with polynomial
intermediate sizes; no binary edge count is expanded.

## Main definitions

* `Planar.Embedding.PolyTime.Wire`: one incidence and its color and orientation.
* `Planar.Embedding.PolyTime.RoutingData.program`: the explicit crossover instruction stream.

## Main results

* `Planar.Embedding.PolyTime.computableInPolyTime_program`: standard PT routing emission.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.Planar.Embedding.PolyTime

open _root_.Turing.MultiTapeTM

/-- A labeled wire with the values preserved by routing. -/
structure Wire where
  /-- Original edge incidence, with a binary edge name. -/
  port : Port ℕ
  /-- Its weight color. -/
  color : Color
  /-- Its original downward orientation. -/
  bit : Bool
  deriving @[expose] DecidableEq

instance : Inhabited Wire := ⟨⟨⟨0, false⟩, .red, false⟩⟩

/-- Encode the binary incidence, color bit, and direction bit as three framed fields. -/
enc_structure encWire : Wire where port : (encPort encNat), color : encColor, bit : encBool

/-- A framed list of explicitly encoded incidence wires. -/
abbrev encWires : List Wire ↪ List Bool := encList encWire

/-- The requested and original wire orders, together with a unary initial offset. -/
structure RoutingData where
  /-- Desired output order. -/
  requested : List Wire
  /-- Original input order. -/
  available : List Wire
  /-- Number of untouched wires to the left. -/
  offset : ℕ

/-- Frame both wire lists and the unary offset in declaration order. -/
enc_structure encRoutingData : RoutingData where
  requested : encWires, available : encWires, offset : encUnary

private def remaining (requested available : List Wire) (i : ℕ) : List Wire :=
  available.filter fun w => !(requested.take i).contains w

private def before (w : Wire) (available : List Wire) : List Wire :=
  available.take (available.idxOf w)

private def pull (offset : ℕ) (w : Wire) (pre : List Wire) : Program :=
  pre.zipIdx.reverse.map fun p =>
    (offset + p.2, Opcode.cross p.1.color w.color p.1.bit w.bit)

/-- Emit the canonical leftward crossing sequence, selecting predecessors by prefix filtering. -/
def RoutingData.program (data : RoutingData) : Program :=
  data.requested.zipIdx.flatMap fun p =>
    pull (data.offset + p.2) p.1 (before p.1 (remaining data.requested data.available p.2))

@[fun_prop]
private theorem computableInPolyTime_pull {α : Type} {input : α ↪ List Bool}
    {offset : α → ℕ} {wire : α → Wire} {pre : α → List Wire}
    (ho : ComputableInPolyTime offset input encUnary)
    (hw : ComputableInPolyTime wire input encWire)
    (hp : ComputableInPolyTime pre input encWires) :
    ComputableInPolyTime (fun x => pull (offset x) (wire x) (pre x))
      input encProgram := by
  unfold pull encProgram Word.Fixed.Language.encProgram
  fun_prop

/-- Prefix filtering, bounded first-occurrence indices, and fixed fragments give PT emission. -/
@[fun_prop]
theorem computableInPolyTime_program :
    ComputableInPolyTime RoutingData.program encRoutingData encProgram := by
  unfold RoutingData.program before remaining
  fun_prop

/-- At most one crossing is emitted per requested/original wire pair. -/
theorem RoutingData.length_program_le (data : RoutingData) :
    data.program.length ≤ data.requested.length * data.available.length := by
  unfold RoutingData.program
  rw [List.length_flatMap]
  have h := List.sum_le_length_nsmul
    (data.requested.zipIdx.map fun p =>
      (pull (data.offset + p.2) p.1 (before p.1
        (remaining data.requested data.available p.2))).length)
    data.available.length (by
      intro n hn
      obtain ⟨p, _hp, rfl⟩ := List.mem_map.mp hn
      simp only [pull, List.length_map, List.length_reverse, List.length_zipIdx, before]
      exact (List.length_take_le' _ _).trans (List.length_filter_le ..))
  simpa using h

end Cslib.Complexity.NCL.Planar.Embedding.PolyTime
