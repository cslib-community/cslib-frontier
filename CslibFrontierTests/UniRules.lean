/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Uni.Det
import Mathlib.Algebra.Ring.Int.Defs

/-! Tests of the rules of the universal machine under ordinary imports:

* the numbers of record kinds and of rules that read no name;
* the forced rule for some modes and record kinds;
* the names read for the support `{[true]}`. -/

set_option linter.privateModule false

namespace CslibFrontierTests.UniRules

open Cslib.Circuits.Arithmetic.Separation.Uni

example : Fintype.card RecKind = 15 := by decide

/-- Evaluating a `cons` record starts decoding; at a `nil` record the value is returned. -/
example : nextRule ({[true]} : Finset (List Bool)) .eval .cons = some (.base .evalCons) ∧
    nextRule ({[true]} : Finset (List Bool)) .eval .nil = some (.base .evalNil) := ⟨rfl, rfl⟩

/-- Reading the input is not forced by the loaded record. -/
example : nextRule ({[true]} : Finset (List Bool)) .parse .nil = none := rfl

example (r : Rule ({[true]} : Finset (List Bool))) (hr : ¬ IsChosen r) :
    nextRule _ (rule (fun _ => (1 : ℤ)) _ r).src (rule (fun _ => (1 : ℤ)) _ r).lk = some r :=
  nextRule_rule r hr

/-- The names for the support `{[true]}` are `[]` and `[true]`. -/
example : prefixes ({[true]} : Finset (List Bool)) = {[], [true]} := by decide

/-- The universal machine starts in `start₀` and halts in `halt`. -/
example : (universalMachine (fun _ => (1 : ℤ)) ({[true]} : Finset (List Bool))).m0 = .start₀ ∧
    (universalMachine (fun _ => (1 : ℤ)) ({[true]} : Finset (List Bool))).mh = .halt := ⟨rfl, rfl⟩

end CslibFrontierTests.UniRules
