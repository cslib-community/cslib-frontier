/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Crypto.Computational.OneWay.WeakNotStrong

/-! Checked clients of the weak one-way function that is not strongly one-way
(Goldreich, Exercise 7.3). -/

set_option linter.privateModule false

namespace CslibFrontierTests.OneWayWeakNotStrong

open Cslib Cslib.Crypto Cslib.Crypto.OneWayEasyHalf

-- Inputs starting with `1` are fixed points; inputs starting with `0` go through `f`.
example : easyHalf (fun _ => []) [true, false] = [true, false] := by simp
example : easyHalf (fun x => x ++ x) [false, true] = [false, true, true] := by simp

-- The easy half makes the construction not one-way, whatever `f` is.
example : ¬ OneWay (easyHalf fun x => x) := not_oneWay _

-- From a one-way function, the construction is weakly one-way.
example {f : List Bool → List Bool} (hf : OneWay f) : WeakOneWay (easyHalf f) := weakOneWay hf

-- The headline.
example {f : List Bool → List Bool} (hf : OneWay f) :
    ∃ g : List Bool → List Bool, WeakOneWay g ∧ ¬ OneWay g :=
  hf.exists_weakOneWay_not_oneWay

end CslibFrontierTests.OneWayWeakNotStrong
