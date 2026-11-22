/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module

public import
  CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.IntervalCount
public import
  CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.IntervalSimulation.InputWindow

/-! Boundary checks for source-input cropping, including both real blank end cells, an interior
window whose artificial ends cannot be read, zero steps, and an empty source word. -/

namespace CslibFrontierTests.IntervalInputWindow

open Turing MultiTapeMachine MultiTapePTM MultiTapeNTM.ChoiceTable Cslib.Turing

/-- Read the source into the control, write the coin to a work tape, and move both heads. Blank
input cells use the coin as the next control, so a spurious boundary would change the run. -/
public def scan (direction : SignType) : MultiTapePTM 1 Bool Bool where
  initial := false
  tr _ symbol _ _ bit := .step
    { inputTape := direction, workTapes := fun _ => (some (some bit), 1),
      output := symbol, state := some (symbol.getD bit) }
    Empty.elim Empty.elim

private def start (p : ℕ) : LocalCfg 1 Bool :=
  ⟨some false, p, fun _ => BiTape.nil, fun _ => 0, .empty⟩

-- The interior window drops two source symbols and retains five of the original nine.
-- Its last two original symbols cannot affect the run. Work writes and the absolute input
-- coordinate survive the translation.
example :
    let result := (scan 1).localRun [false, true, false, true, false, true, false, true, true]
      [true, false] (start 5)
    (result.inputPos, result.state, result.workTapePos 0, (result.workTapes 0).read (-1)) =
      (7, some true, 2, some false) := by
  have h := localRun_inputWindow (scan 1)
    [false, true, false, true, false, true, false, true, true] [true, false] (start 5) 2
    (by decide) (by decide)
  dsimp only
  rw [← h]
  decide

-- Moving toward the artificial left end also stops at a genuine source cell.
example :
    let result := (scan (-1)).localRun [false, true, false, true, false, true, false, true, true]
      [true, false] (start 5)
    (result.inputPos, result.state) = (3, some true) := by
  have h := localRun_inputWindow (scan (-1))
    [false, true, false, true, false, true, false, true, true] [true, false] (start 5) 2
    (by decide) (by decide)
  dsimp only
  rw [← h]
  decide

-- At the real left marker the head stays clamped; it must read blank twice.
example :
    let result := (scan (-1)).localRun [true, true, true, true] [true, false] (start 0)
    (result.inputPos, result.state, result.track) = (0, some false, OutputTrack.empty) := by
  have h := localRun_inputWindow (scan (-1)) [true, true, true, true] [true, false] (start 0) 2
    (by decide) (by decide)
  dsimp only
  rw [← h]
  decide

-- Cropping an input near its real right marker preserves that marker and the clamp.
example :
    let result := (scan 1).localRun [false, false, true, true] [true, false] (start 5)
    (result.inputPos, result.state, result.track) = (5, some false, OutputTrack.empty) := by
  have h := localRun_inputWindow (scan 1) [false, false, true, true] [true, false] (start 5) 2
    (by decide) (by decide)
  dsimp only
  rw [← h]
  decide

-- The empty source still has two distinct blank end positions. A right move reaches position
-- one, then stays there, with no source symbols emitted.
example :
    let result := (scan 1).localRun [] [true, false] (start 0)
    (result.inputPos, result.state, result.track) = (1, some false, OutputTrack.empty) := by
  have h := localRun_inputWindow (scan 1) [] [true, false] (start 0) 2
    (by decide) (by decide)
  dsimp only
  rw [← h]
  decide

-- A zero-step crop may end immediately before the starting right marker; restoring the origin
-- still returns exactly the same initial storage.
example :
    let result := (scan 1).localRun [true, false, true] [] (start 4)
    (result.inputPos, result.state, result.track) = (4, some false, OutputTrack.empty) := by
  have h := localRun_inputWindow (scan 1) [true, false, true] [] (start 4) 0
    (by decide) (by decide)
  dsimp only
  rw [← h]
  decide

/-- A two-step interval strictly inside a nine-symbol source, with one accepted coin string. -/
public def interior : IntervalData 1 Bool :=
  ⟨[false, true, false, true, false, true, false, true, true], 2,
    fun head => head.elim 2 (fun _ => 0), fun _ => 1,
    (some false, fun _ => 0, .empty), fun _ => List.replicate 6 none,
    (some true, fun _ => 0, .other),
    fun _ => [none, none, some true, some false, none, none]⟩

/-- Exactly one of the four coin strings writes the prescribed work cells; the control also
depends on source symbols strictly inside the input. -/
public theorem count_interior_interval : IntervalData.count (scan 1) interior = 1 := by
  decide

-- The prepared native record drops two symbols, retains five, and keeps its relative head
-- position short. The original outgoing coordinates and work windows remain part of the record.
example : (IntervalData.InputWindow.prepare interior).origin = 2 ∧
    (IntervalData.InputWindow.prepare interior).position = 3 ∧
    (IntervalData.InputWindow.prepare interior).interval.input =
      [false, true, false, true, false] := by
  decide

-- An out-of-range incoming coordinate falls back to the real left marker before cropping.
example : (IntervalData.InputWindow.prepare { interior with J := fun _ => -10 }).origin = 0 ∧
    (IntervalData.InputWindow.prepare { interior with J := fun _ => -10 }).position = 0 ∧
    (IntervalData.InputWindow.prepare { interior with J := fun _ => -10 }).interval.input =
      interior.input.take 5 := by
  decide

example : (IntervalData.InputWindow.prepare interior).test (scan 1) [true, false] = true := by
  rw [IntervalData.InputWindow.test_prepare (scan 1) interior [true, false] (by decide)]
  decide

example : (IntervalData.InputWindow.prepare interior).test (scan 1) [true, true] = false := by
  rw [IntervalData.InputWindow.test_prepare (scan 1) interior [true, true] (by decide)]
  decide

-- The original interval is framed, then the binary origin; the relative position stays unary.
example (d : IntervalData.InputWindow 1 Bool) : encInputWindow d =
    MultiTapeTM.encPair encIntervalData
      (MultiTapeTM.encPair MultiTapeTM.encNat MultiTapeTM.encUnary)
      (d.interval, d.origin, d.position) := encInputWindow_apply d

example : MultiTapeTM.ComputableInPolyTime
    (fun p : IntervalData.InputWindow 1 Bool × List Bool => p.1.test (scan 1) p.2)
    (MultiTapeTM.encPair encInputWindow MultiTapeTM.encBits) MultiTapeTM.encBool :=
  IntervalData.InputWindow.computableInPolyTime_test (scan 1)
    (MultiTapeTM.ComputableInPolyTime.fst _ _) (MultiTapeTM.ComputableInPolyTime.snd _ _)

-- Even an invalid incoming coordinate retains the original fallback to the left end.
-- Width zero has no valid outgoing offset and hence no qualifying coin string.
example : (scan 1).localIntervalCount 0 [true] (fun _ => -10) (fun _ => 0)
    (some false, fun _ => 3, .empty) (fun _ => [])
    (some false, fun _ => 0, .empty) (fun _ => []) = 0 := by
  decide

open MultiTapeATM in
/-- The native counter extracts an interior source window with nonzero origin, decodes it and
checks every bit of the original count. One finite machine handles every host and both claims;
the original nine-symbol source contributes outside the metadata power. -/
public theorem native_interior_count : ∃ (u : ℕ) (src : Fin u) (Q : Type) (_ : Finite Q)
    (atm : MultiTapeATM u Bool Q) (C E : ℕ),
    ∀ (host : List Bool) (bit : Fin 3) (claim : Bool),
      let a : IntervalCount.Request 1 Bool := ⟨interior, bit.val, claim⟩
      let cfg := SharedWordFork.start src atm host (IntervalCount.encRequest a) 0
      let time := C * (9 + ((IntervalCount.encRequest
        { a with interval := { a.interval with input := [] } }).length + 1) ^ E + 1)
      atm.HaltsWithin time cfg ∧ (atm.AcceptsWithin time cfg ↔
        (1 : ℕ).testBit bit.val = claim) := by
  obtain ⟨u, src, Q, hQ, atm, C, E, h⟩ := IntervalCount.exists_evaluator (scan 1)
  refine ⟨u, src, Q, hQ, atm, C, E, ?_⟩
  intro host bit claim a cfg time
  obtain ⟨hh, ha⟩ := h host a bit.isLt
  refine ⟨hh, ha.trans ?_⟩
  change (IntervalData.count (scan 1) interior).testBit bit.val = claim ↔ _
  rw [count_interior_interval]

end CslibFrontierTests.IntervalInputWindow
