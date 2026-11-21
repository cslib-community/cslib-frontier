/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RootEndpointAddress
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RootEndpointFinish
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Sum
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeOptionPrimitives

/-!
# Resolving a short address and a tagged scanner answer

The copy/edge classifier supplies an optional address and the schedule scan supplies an
independently computed tagged answer. Only a work continuation reads that answer. Direct
addresses already determine the row and column, even when the unused scan rejects.
-/

public section

namespace Turing.MultiTapeTM.RootEndpointResolveShort

open RootEndpointAddress

/-- Short address result paired with the actual scan answer. -/
abbrev Input := Option Address × Option (Option ℕ)

/-- The optional address is framed. The final word has explicit validity/found tags. -/
abbrev encInput : Input ↪ List Bool := encPair encResult ScheduleEndpointAnswer.encAnswer

/-- Resolve a present address, reading the supplied scan answer only for a work row. -/
@[expose] def atAddress (p : Option (Option ℕ) × Address) : Option (ℕ × ℕ) :=
  if p.2.row.isLeft then some (p.2.row.getLeft?.getD 0, p.2.column)
  else RootEndpointFinish.run ⟨p.1, (p.2.row.getRight?.getD ⟨0, 0, 0⟩).sink, p.2.column⟩

/-- Select the two endpoint keys determined by the address and (for work edges) the scan. -/
@[expose] def run (p : Input) : Option (ℕ × ℕ) :=
  p.1.elim none fun address => atAddress (p.2, address)

/-- Rejected edge numbers return no endpoint, independently of the scan. -/
@[simp] theorem run_none (answer : Option (Option ℕ)) : run (none, answer) = none := rfl

/-- Direct addresses retain both keys even on an unsuccessful scan. -/
@[simp] theorem run_direct (row column : ℕ) (answer : Option (Option ℕ)) :
    run (some ⟨.inl row, column⟩, answer) = some (row, column) := rfl

/-- Work addresses resolve the tagged answer using the original edge's sink and column. -/
@[simp] theorem run_work (w : Work) (column : ℕ) (answer : Option (Option ℕ)) :
    run (some ⟨.inr w, column⟩, answer) =
      RootEndpointFinish.run ⟨answer, w.sink, column⟩ := rfl

private theorem atAddress_polyTime : ComputableInPolyTime atAddress
    (encPair ScheduleEndpointAnswer.encAnswer encAddress) RootEndpointFinish.encOutput := by
  have ha := ComputableInPolyTime.snd ScheduleEndpointAnswer.encAnswer encAddress
  have hr := encAddress_row_polyTime ha
  have hc := encAddress_column_polyTime ha
  have hl := (ComputableInO.getLeft?_deg encNat encWork).computableInPolyTime.comp hr
  have hw := (ComputableInO.getRight?_deg encNat encWork).computableInPolyTime.comp hr
  have hd := ComputableInPolyTime.optionGetDWithInput hl (.const 0)
  have hs := encWork_sink_polyTime
    (ComputableInPolyTime.optionGetDWithInput hw (.const ⟨0, 0, 0⟩))
  exact ComputableInPolyTime.ite
    ((ComputableInO.isLeft_deg encNat encWork).computableInPolyTime.comp hr)
    ((ComputableInPolyTime.optionSome (encPair encNat encNat)).comp (hd.prod hc))
    (RootEndpointFinish.computableInPolyTime_run.comp
      (RootEndpointFinish.encInput_mk_polyTime
        (ComputableInPolyTime.fst ScheduleEndpointAnswer.encAnswer encAddress) hs hc))

/-- The native cost of resolving both answers is polynomial in their short serialized words. -/
theorem computableInPolyTime_run :
    ComputableInPolyTime run encInput RootEndpointFinish.encOutput := by
  apply ComputableInPolyTime.optionElimWithInput (body := fun p addr => atAddress (p.2, addr))
    (ComputableInPolyTime.fst encResult ScheduleEndpointAnswer.encAnswer)
    (ComputableInPolyTime.const none)
  apply atAddress_polyTime.comp
  exact ((ComputableInPolyTime.snd encResult ScheduleEndpointAnswer.encAnswer).comp
    (ComputableInPolyTime.fst encInput encAddress)).prod
      (ComputableInPolyTime.snd encInput encAddress)

end Turing.MultiTapeTM.RootEndpointResolveShort
