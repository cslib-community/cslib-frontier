/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Complexity.Classes.Padding.NondeterministicExponential
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Exponential

/-!
# Tests for polynomial padding into `NTIME (2 ^ n)`

`Cslib.Complexity.polynomialPadded_mem_NTIME_two_pow` at `k = 1`, for the language of all words,
which is in `P` and so in `NTIME (n ^ j)` for some `j`, hence in `NTIME (2 ^ n ^ 1)`:

* the hypotheses are satisfiable, and the padded language `polynomialPadded univ 2` is in
  `NTIME (2 ^ n)`;
* the padded language is neither empty nor everything: a word padded to the required length is
  in it, and the empty word is not;
* membership goes through the total decoder `unframe` and a length test, not through well-formed
  frames: `[true]`, with no terminating frame bit, decodes to `[]` and is in the language.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Computability.Complexity.Classes.Padding.NondeterministicExponential

open Cslib Cslib.Complexity Turing.MultiTapeTM

/-- The language of all words is in `NTIME (2 ^ n ^ 1)`. -/
theorem univ_mem_NTIME_two_pow :
    (Set.univ : Set (List Bool)) ∈ NTIME encBits (fun n => 2 ^ n ^ 1) := by
  obtain ⟨j, hj⟩ := mem_P_iff_exists_mem_DTIME.1 (univ_mem_P (enc := encBits))
  obtain ⟨C, hC⟩ := Cslib.PolynomiallyBounded.exists_le_mul_two_pow
    (p := fun n => n ^ j) (by fun_prop)
  refine NTIME_mono_of_le_mul_add (C := C) (fun n => ?_) (DTIME_subset_NTIME hj)
  have := hC n
  simp only [pow_one]
  omega

/-- **The padded language of `univ` is in `NTIME (2 ^ n)`.** -/
theorem padded_univ_mem_NTIME :
    polynomialPadded Set.univ (1 + 1) ∈ NTIME encBits (fun n => 2 ^ n) :=
  polynomialPadded_mem_NTIME_two_pow le_rfl univ_mem_NTIME_two_pow

/-- A word `frame [true] ++ 1 ^ 4` is long enough: `(1 + 1) ^ 2 ≤ 4`. -/
example : frame [true] ++ List.replicate 4 true ∈ polynomialPadded Set.univ (1 + 1) :=
  (frame_append_replicate_mem_polynomialPadded_iff (by norm_num)).2 trivial

/-- The decoder is total: `[true]` has no terminating frame bit, yet `unframe [true] = []` and
`(0 + 1) ^ 2 ≤ 1`, so `[true]` is in the padded language of `univ`. -/
example : [true] ∈ polynomialPadded Set.univ (1 + 1) :=
  mem_polynomialPadded_iff.2 ⟨by decide, trivial⟩

/-- The empty word is not padded to the length `(0 + 1) ^ 2`. -/
example : ([] : List Bool) ∉ polynomialPadded Set.univ (1 + 1) := by
  simp

/-- Padding is not trivial: `frame y`, `|y| = 3`, with one padding bit is shorter than `4 ^ 2`. -/
example :
    frame [true, true, true] ++ List.replicate 1 true ∉ polynomialPadded Set.univ (1 + 1) := by
  intro h
  have := (mem_polynomialPadded_iff.1 h).1
  rw [unframe_frame_append] at this
  simp at this

end CslibFrontierTests.Computability.Complexity.Classes.Padding.NondeterministicExponential
