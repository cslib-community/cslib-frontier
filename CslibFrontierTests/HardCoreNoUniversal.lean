/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Crypto.Computational.HardCore.NoUniversal

/-! Checked clients of the impossibility of a universal hard-core predicate
(Goldreich, Exercise 7.8). -/

set_option linter.privateModule false

namespace CslibFrontierTests.HardCoreNoUniversal

open Cslib Cslib.Crypto Turing.MultiTapeTM

-- The appended bit is the last bit of the image.
example (f : List Bool → List Bool) (b : List Bool → Bool) (x : List Bool) :
    lastBit (appendPredicate f b x) = b x := by
  simp [appendPredicate]

-- Appending a polynomial-time bit to a one-way function keeps it one-way.
example {f : List Bool → List Bool} (hf : OneWay f) :
    OneWay (appendPredicate f lastBit) :=
  hf.appendPredicate computableInPolyTime_lastBit

-- No predicate, efficient or not, is a hard-core of its own appended function.
example (b : List Bool → Bool) : ¬ HardCore (appendPredicate (fun x => x) b) b :=
  not_hardCore_appendPredicate _ b

-- The headline: given a one-way function, no predicate is a hard-core of every one-way function.
example {f : List Bool → List Bool} (hf : OneWay f) :
    ¬ ∃ b : List Bool → Bool, ∀ g : List Bool → List Bool, OneWay g → HardCore g b :=
  hf.not_exists_universal_hardCore

end CslibFrontierTests.HardCoreNoUniversal
