/-
Copyright (c) 2026 Peter Rindal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Rindal
-/

module
-- upstream: local-only (test)

public import CslibFrontierTests.Crypto.UCComputational.Stateful
public import CslibFrontierTests.Crypto.UCComputational.WitnessSelection

/-!
# Tests of computational UC replacement

These tests certify the PRG reduction under both static corruption sets, check the
route that carries its challenge, and exercise a caller that retains an acknowledgment.
An admitted tag test also rules out forwarding as a witness for child emulation.
-/
