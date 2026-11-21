/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RootPredecessorContext

open Turing.MultiTapeTM RootPredecessorContext

-- A shared buffer can serve both candidates without reparsing a supplied graph description.
example (a : RootPredecessorQuery.Input) (i j : ℕ) :
    (inputOf (word a, i)).context.candidate = i ∧
    (inputOf (word a, j)).context.edge = a.context.edge ∧
    (inputOf (word a, j)).raw = a.raw := by simp [withCandidate]

-- The empty buffer decodes to a zero-row graph and every lookup rejects.
example (k : ℕ) : predicate k ([], 0) = false := by
  simp [predicate, RootPredecessorQuery.query, RootPredecessorQuery.finishInput,
    RootPredecessorQuery.request, Cslib.SeededPredecessorFinish.run]
