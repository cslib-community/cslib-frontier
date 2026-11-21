/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleEndpointTransport
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option

/-!
# Completing a root endpoint from a schedule answer

A found interval is the row key. Exhaustion selects the supplied sink. Both cases pair the row
with the supplied subdivision column. An invalid scanner request yields no pair.
-/

public section

namespace Turing.MultiTapeTM.RootEndpointFinish

open ComputableInPolyTime

/-- A scanner answer and its two short finishing keys. -/
structure Input where
  /-- The answer emitted by the schedule endpoint machine. -/
  answer : Option (Option ℕ)
  /-- The original edge's sink on valid exhaustion. -/
  sink : ℕ
  /-- The subdivision column shared by the two halves of an edge. -/
  column : ℕ
  deriving DecidableEq

/-- Framed validity/found-tag answer, framed binary sink, then binary column. -/
enc_structure encInput : Input where
  answer : ScheduleEndpointAnswer.encAnswer, sink : encNat, column : encNat

/-- Empty word on rejection, or a true tag, a framed binary row and a binary column. -/
abbrev encOutput : Option (ℕ × ℕ) ↪ List Bool := encOption (encPair encNat encNat)

/-- The finishing input length includes the actual tagged answer and two binary keys. -/
theorem length_encInput (a : Input) :
    (encInput a).length = 2 * (ScheduleEndpointAnswer.encAnswer a.answer).length +
      2 * a.sink.bits.length + a.column.bits.length + 2 := by
  simp [encInput_apply, encInputFields, encPair_apply, encNat_apply]
  omega

/-- Resolve the row from the answer and pair it with the subdivision column. -/
@[expose] def run (a : Input) : Option (ℕ × ℕ) :=
  a.answer.map fun next => (next.getD a.sink, a.column)

/-- The encoded result fits in the serialized input even when exhaustion selects the sink. -/
theorem length_output_le (a : Input) : (encOutput (run a)).length ≤ (encInput a).length := by
  rw [length_encInput]
  rcases a with ⟨(_ | (_ | n)), sink, column⟩ <;>
    simp [run, encOutput, ScheduleEndpointAnswer.encAnswer]
  all_goals omega

/-- The native finisher pays for the conversion of the emitted tags before reading the row. -/
theorem computableInPolyTime_run : ComputableInPolyTime run encInput encOutput := by
  have ha : ComputableInPolyTime Input.answer encInput (encOption (encOption encNat)) :=
    ScheduleEndpointAnswer.computableInDegree_standard.computableInPolyTime.comp (by fun_prop)
  have hrow : ComputableInPolyTime (fun p : Input × Option ℕ => p.2.getD p.1.sink)
      (encPair encInput (encOption encNat)) encNat :=
    optionGetDWithInput (by fun_prop) (by fun_prop)
  exact ha.optionMapWithInput (hrow.prod (by fun_prop))

end Turing.MultiTapeTM.RootEndpointFinish
