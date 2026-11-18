/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.CDCL.System

/-! # Phase saving for the CDCL solver

MiniSat's choice of polarity for a decision (with `phase_saving = 2`). Every variable has a saved
*phase*, initially `false`, so a fresh variable is decided negative, as MiniSat's default polarity
does. When a backjump unassigns variables, each one's phase becomes the value it had on the trail
(`Phases.save`), and a later decision on it takes that value again (`Phases.get`). The solver thus
returns to the part of the search space it left, keeping the assignments of the subproblems it
had solved.

The polarity of a decision does not affect correctness.

## Main definitions

* `Cslib.Algorithms.Lean.CDCL.Phases`: the saved phases.
* `Cslib.Algorithms.Lean.CDCL.Phases.save`: saving the phases of the literals undone by a
  backjump.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.CDCL

open Cslib.Logic.PL

/-- **Saved phases**: a polarity for each variable, by index; variables past the end have the
phase `false`. -/
structure Phases where
  /-- The saved polarity of each variable. -/
  saved : Array Bool

/-- The initial phases of the variables below `n`: all `false`. -/
def Phases.init (n : ℕ) : Phases := ⟨Array.replicate n false⟩

/-- The phase of the variable `v`: the polarity of its next decision. -/
def Phases.get (P : Phases) (v : ℕ) : Bool := P.saved.getD v false

/-- **Saving** the phases of the literals of `M`, which a backjump undoes: each variable takes the
value it had. -/
def Phases.save (P : Phases) (M : Trail) : Phases :=
  ⟨(Trail.lits M).foldl (fun a l => a.setIfInBounds l.1 l.2) P.saved⟩

end Cslib.Algorithms.Lean.CDCL
