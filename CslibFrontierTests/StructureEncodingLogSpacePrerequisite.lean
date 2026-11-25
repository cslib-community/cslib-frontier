/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (structure-encoding logspace prerequisite regression test)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure

/-! The base command works below logspace composition; opting in requires its rules first. -/

open Turing.MultiTapeTM

namespace CslibFrontierTests.StructureEncodingLogSpacePrerequisite

/-- A single word, so the test isolates the missing certificate family. -/
public structure Packet where
  /-- The payload word. -/
  bits : List Bool

/-- The base command remains usable without the logspace composition library. -/
enc_structure encPacket : Packet where bits : encBits

example (p : Packet) : encPacket p = p.bits := rfl

/--
error: enc_structure logspace: import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Words before requesting logspace rules (missing `Turing.MultiTapeTM.ComputableInLogSpace`)
-/
#guard_msgs in
enc_structure encMissing : Packet logspace where bits : encBits

-- The failed prerequisite check happens before any generated declaration is added.
run_cmd do
  let env ← Lean.getEnv
  for suffix in ["", "Fields", "_apply", "_fields_deg", "_fields_logSpace"] do
    let decl :=
      (`CslibFrontierTests.StructureEncodingLogSpacePrerequisite.encMissing).appendAfter suffix
    if env.contains decl then
      throwError "failed enc_structure declared {decl}"

end CslibFrontierTests.StructureEncodingLogSpacePrerequisite
