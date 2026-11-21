/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Crypto.Computational.OneWay.IterateCounterexample

/-! Clients of the one-way function with non-one-way iterates (Arora–Barak draft, Chapter 10,
Exercise 4): a fractional exponent, a natural power, the explicit construction, and its fixed
output length with equal second images. -/

set_option linter.privateModule false

namespace CslibFrontierTests.OneWayIterateCounterexample

open Cslib.Crypto Cslib.Crypto.IterateCounterexample

/-- The exponent `c = 1 / 2`: some one-way function has a non-one-way `⌈√|x|⌉`-fold iterate. -/
example (h : ∃ g : List Bool → List Bool, OneWay g) :
    ∃ f : List Bool → List Bool, OneWay f ∧
      ¬ OneWay (fun x => f^[⌈(x.length : ℝ) ^ (1 / 2 : ℝ)⌉₊] x) := by
  obtain ⟨f, hf, -, hiter⟩ := exists_oneWay_not_oneWay_iterate_ceil_rpow h
  exact ⟨f, hf, hiter _ (by norm_num)⟩

/-- The natural power `n ^ 2`, through the general count theorem. -/
example (h : ∃ g : List Bool → List Bool, OneWay g) :
    ∃ f : List Bool → List Bool, OneWay f ∧ ¬ OneWay (fun x => f^[x.length ^ 2] x) := by
  obtain ⟨f, hf, -, hiter⟩ := exists_oneWay_not_oneWay_iterate h
  refine ⟨f, hf, hiter (fun n => n ^ 2) (Filter.eventually_atTop.2 ⟨2, fun n hn => ?_⟩)⟩
  nlinarith

/-- The explicit construction: one-way, while already its two-step iterate is not. -/
example {g : List Bool → List Bool} {length : ℕ → ℕ} (hg : OneWay g)
    (hlen : ∀ input, (g input).length = length input.length) :
    OneWay (collapse g) ∧ ¬ OneWay (fun x => (collapse g)^[2] x) :=
  ⟨oneWay_collapse hg,
    not_oneWay_iterate_collapse (k := fun _ => 2) hlen
      (Filter.Eventually.of_forall fun _ => le_rfl)⟩

/-- Two distinct inputs of the same length, one low-zero and one not, have equal output lengths
and equal second images. -/
example {g : List Bool → List Bool} {length : ℕ → ℕ}
    (hlen : ∀ input, (g input).length = length input.length) :
    (collapse g [false, false]).length = (collapse g [true, true]).length ∧
      (collapse g)^[2] [false, false] = (collapse g)^[2] [true, true] :=
  ⟨by rw [length_collapse, length_collapse, hlen, hlen]; rfl, iterate_collapse_eq hlen 0 rfl⟩

end CslibFrontierTests.OneWayIterateCounterexample
