/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Crypto.Computational.OneWay.LengthPreserving

/-! Checked clients of the length-preserving one-way function construction
(Goldreich, Exercise 7.1). -/

set_option linter.privateModule false

namespace CslibFrontierTests.OneWayLengthPreserving

open Cslib Cslib.Crypto Cslib.Crypto.OneWayLengthPreserving

-- Fitting produces exactly the requested number of bits, also for overlong words.
example : (fit 3 [true, false, true, true]).length = 3 := by simp

-- Short words are recovered from their fitted form.
example {word word' : List Bool} (hword : word.length ≤ 3) (hword' : word'.length ≤ 3)
    (h : fit 7 word = fit 7 word') : word = word' :=
  word_eq_of_fit_eq (by omega) (by omega) h

-- The construction preserves lengths for every function and output length, one-way or not.
example (x : List Bool) : (lengthPreserving (fun _ => []) (fun _ => 0) x).length = x.length := by
  simp

-- The headline: a one-way function gives a length-preserving one-way function.
example {f : List Bool → List Bool} (hf : OneWay f) :
    ∃ f' : List Bool → List Bool, OneWay f' ∧ ∀ x, (f' x).length = x.length :=
  hf.exists_lengthPreserving

end CslibFrontierTests.OneWayLengthPreserving
