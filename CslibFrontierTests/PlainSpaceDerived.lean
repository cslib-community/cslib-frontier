/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of the plain space proof migration)

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Space.Reachability
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Space.SavitchWalk
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Words
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolySpace
import Lean

open Turing.MultiTapeTM

-- Zero is a valid charged-space envelope, even with unbounded input and nonempty output.
example : ComputableInSpace (fun _ : List Bool => [true, false]) encBits encBits
    (fun _ => 0) := by
  exact (ComputableInSpace.constZero (encIn := encBits) (encB := encBits) [true]).append
    (ComputableInSpace.constZero (encIn := encBits) (encB := encBits) [false]) (fun _ => rfl)

-- The counter's plain degree witness serves an ordinary space client.
example : ComputableInSpace Cslib.BitString.increment encBits encBits
    (fun w => w.length) := by
  exact ComputableInSpace.of_inO ComputableInDegree.increment.inO_one

-- Logspace concatenation does not require charging the output against the logarithmic budget.
example : ComputableInLogSpace (fun w : List Bool => w ++ w) encBits encBits := by
  exact ComputableInLogSpace.append
    (ComputableInLogSpace.of_eq fun _ => rfl)
    (ComputableInLogSpace.of_eq fun _ => rfl) (fun _ => rfl)

-- Search suffixes because private names have a module/serial-number prefix. An unresolved
-- public spelling would already have failed before deletion and would not test this migration.
run_cmd do
  for (name, _) in (← Lean.getEnv).constants.toList do
    if name.toString.endsWith ".computableTidilyInO_roundStep" ||
        name.toString.endsWith ".computableTidilyInO_savitch" then
      throwError "superseded private tidy proof remains: {name}"
