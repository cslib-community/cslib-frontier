/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (project test driver)

public import CslibFrontierTests.Crypto.HMACMGF1

/-!
# Native project test driver

This executable depends on the complete `CslibFrontierTests` library and then runs the expensive
HMAC and MGF1 known-answer tests as native code. Keeping these checks out of module elaboration
prevents SHA-2 evaluation from holding the ordinary test-build critical path open.
-/

public def main : IO UInt32 := do
  let checks := HMACMGF1Tests.hmacMGF1Checks
  let failures := checks.filter fun check => !check.2
  if failures.isEmpty then
    IO.println s!"HMAC/MGF1 native fixtures passed ({checks.length})"
    return 0
  else
    for failure in failures do
      IO.eprintln s!"HMAC/MGF1 native fixture failed: {failure.1}"
    return 1
