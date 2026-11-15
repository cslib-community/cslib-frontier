/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.SecondPreimageResistant.Relations

/-!
# Tests for second-preimage resistance implications and separations

Checks for `CslibFrontier/Crypto/Computational/SecondPreimageResistant/Relations.lean` as a
`module` client with ordinary imports:

* Concrete evaluations of `ignoreHeadBit`, `flipHeadBit`, and `plantEasyBranch`.
* The Section 8.11.1 separation (`not_secondPreimageResistant_ignoreHeadBit_id`) and the
  bit-string Exercise 8.23(c) separation (`secondPreimageResistant_plantEasyBranch_id` and
  `not_oneWay_plantEasyBranch_id`), giving an explicit unconditional function `plantEasyBranch 2 id`
  that is `SecondPreimageResistant` and `¬ OneWay`.
* Necessity of the super-polynomial compression premise in
  `SecondPreimageResistant.oneWay_of_outputLength`: for `f = id` (`outLen n = n`), `id` is
  `SecondPreimageResistant` (`secondPreimageResistant_id`) and satisfies `hlen`, yet `¬ OneWay id`
  because `2 ^ n / 2 ^ n = 1` is not negligible (`not_oneWay_id`).
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.SecondPreimageResistantRelations

open Cslib Cslib.Crypto Cslib.ProbComp Cslib.Probability
open Turing.MultiTapeTM
open scoped NNReal ENNReal

example : flipHeadBit [false, true] = [true, true] := rfl

example : flipHeadBit [] = [true] := rfl

example : ignoreHeadBit id [false, true] = ignoreHeadBit id (flipHeadBit [false, true]) := rfl

example : plantEasyBranch 2 id [false, false, true] = [true, true] := rfl

example : plantEasyBranch 2 id [true, false, true] = [false, true, false, true] := rfl

/-- The identity on bit strings is unconditionally `SecondPreimageResistant`. -/
theorem secondPreimageResistant_id : SecondPreimageResistant id :=
  SecondPreimageResistant.of_injective (ComputableInPolyTime.id' (encIn := encBits))
    Function.injective_id

/-- **Necessity of compression in `SecondPreimageResistant.oneWay_of_outputLength`**: `id` is
`SecondPreimageResistant` and length-preserving (`outLen n = n`), yet `¬ OneWay id`. -/
theorem not_oneWay_id : ¬ OneWay id :=
  not_oneWay_of_inverse id (fun _ y => y)
    (ComputableInPolyTime.id' (encIn := encBits)).isPPT (fun _ => rfl)

/-- `ignoreHeadBit id` is not second-preimage resistant. -/
theorem not_secondPreimageResistant_ignoreHeadBit_id :
    ¬ SecondPreimageResistant (ignoreHeadBit id) :=
  not_secondPreimageResistant_ignoreHeadBit id

/-- Explicit unconditional witness for Exercise 8.23(c) on bit strings: `plantEasyBranch 2 id` is
`SecondPreimageResistant` and `¬ OneWay`. -/
theorem secondPreimageResistant_plantEasyBranch_id :
    SecondPreimageResistant (plantEasyBranch 2 id) :=
  secondPreimageResistant_id.plantEasyBranch 2

theorem not_oneWay_plantEasyBranch_id : ¬ OneWay (plantEasyBranch 2 id) :=
  not_oneWay_plantEasyBranch 2 id

end CslibFrontierTests.Crypto.SecondPreimageResistantRelations
