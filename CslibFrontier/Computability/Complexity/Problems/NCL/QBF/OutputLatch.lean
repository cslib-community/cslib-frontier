/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.Latch
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Realization
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Enumeration

/-!
# The output latch and outer controls

Place the latch of [HearnDemaine2005, Figure 6] above a QBF body. Its lock is the body's sat
input, so a successful body unlocks the latch. Its red branches end in a cap; a free blue source
provides trying. The latch has canonical configurations for both memory values and both control
directions. Three internal reversals record success while the lock is inactive.

## Main definitions

* `Cslib.Complexity.NCL.QBF.OutputLatch.diagram`: a closed source for the two outer controls.
* `Cslib.Complexity.NCL.QBF.OutputLatch.canonical`: canonical memory and control settings.

## Main results

* `Cslib.Complexity.NCL.QBF.OutputLatch.record`: set the memory while sat is active, keeping
  both control directions fixed.
* `Cslib.Complexity.NCL.QBF.OutputLatch.canonical_flip_sat`,
  `Cslib.Complexity.NCL.QBF.OutputLatch.canonical_flip_try`: follow control reversals without
  changing any other edge.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.QBF.OutputLatch

open Diagram Gate

local notation "B" => Color.blue
local notation "R" => Color.red

/-- The output latch beside a free try source, with its red branches terminated. Its bottom
wires are the body's sat and try inputs, in that order. -/
@[expose] def diagram : Diagram Gate [] [B, B] :=
  (latch.tensor (gen start)).comp
    ((pad [B] (moveLeft [R, R] B []) []).comp ((Diagram.id [B, B]).tensor (gen cap)))

/-- The latch inside the output controller. -/
@[expose] def latchOcc : Occurrence latch diagram := .compLeft _ (.tensorLeft _ .refl)

/-- The output memory, which records a successful run of the body. -/
@[expose] def mem : diagram.Edge := latchOcc.emb Latch.mem

/-- The lock of the output latch is the body's sat input. -/
@[expose] def sat : diagram.Edge := diagram.bottom 0

/-- The freely controlled try input of the body. -/
@[expose] def attempt : diagram.Edge := diagram.bottom 1

theorem latch_lock : latchOcc.emb Latch.lock = sat := by decide +kernel

attribute [local instance] Diagram.decidableLegal

/-- A canonical memory value with arbitrary sat and try directions. All red branches are
inactive. Only the two blue branch directions and the memory depend on `recorded`. -/
@[expose] def canonical (recorded response trying : Bool) :
    Realization Gate.interp diagram [] [response, trying] where
  orient := fun e => ((if response then [0] else []) ++
    (if recorded then [1, 4] else [2]) ++ (if trying then [6] else [])).contains (diagram.num e)
  legal := by cases recorded <;> cases response <;> cases trying <;> decide +kernel
  top_eq := rfl
  bot_eq := by cases recorded <;> cases response <;> cases trying <;> decide +kernel

@[simp] theorem canonical_mem (recorded response trying : Bool) :
    (canonical recorded response trying).orient mem = recorded := by
  cases recorded <;> cases response <;> cases trying <;> decide +kernel

/-- Follow a reversal of sat with the memory and try direction fixed. -/
theorem canonical_flip_sat (recorded response trying : Bool) :
    (canonical recorded (!response) trying).orient =
      reverse (canonical recorded response trying).orient sat := by
  cases recorded <;> cases response <;> cases trying <;> decide +kernel

/-- Follow a reversal of try with the memory and sat direction fixed. -/
theorem canonical_flip_try (recorded response trying : Bool) :
    (canonical recorded response (!trying)).orient =
      reverse (canonical recorded response trying).orient attempt := by
  cases recorded <;> cases response <;> cases trying <;> decide +kernel

private def numbered (n : Fin 7) : diagram.Edge := diagram.numEquiv.symm n

private def recordMoves : List diagram.Edge := [1, 4, 2].map numbered

private theorem record_checked (trying : Bool) :
    InnerRun Gate.interp diagram (canonical false false trying).orient recordMoves ∧
      reverseAll (canonical false false trying).orient recordMoves =
        (canonical true false trying).orient := by
  cases trying <;> decide +kernel

/-- Record success while the body unlocks the latch. Every boundary direction stays fixed. -/
theorem record (trying : Bool) : InnerReach Gate.interp diagram
    (canonical false false trying).orient (canonical true false trying).orient := by
  obtain ⟨hrun, hend⟩ := record_checked trying
  exact hend ▸ hrun.innerReach

end Cslib.Complexity.NCL.QBF.OutputLatch
