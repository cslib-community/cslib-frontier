/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.PH.Kannan

/-!
# Languages in `PSPACE` that are hard at all large lengths

For every `k`, some language in `PSPACE` has slices that need more than `(n + 1) ^ k` De Morgan
gates at all large lengths `n` (`Cslib.Complexity.EasyWitness.exists_mem_PSPACE_eventually_lt`):
Kannan's language, which is in `Σ₃` ([Kannan1982]), so in `PSPACE`. This is the hard language
against which the easy-witness lemma of [ImpagliazzoKabanetsWigderson2002] derives its
contradiction: it is hard at every large length, so a family of small circuits that computes it
at infinitely many lengths cannot exist.

## Main results

* `Cslib.Complexity.EasyWitness.exists_mem_PSPACE_eventually_lt`.

## References

* [R. Kannan, *Circuit-size lower bounds and non-reducibility to sparse sets*][Kannan1982]
* [R. Impagliazzo, V. Kabanets, A. Wigderson, *In search of an easy witness: exponential time vs.
  probabilistic polynomial time*][ImpagliazzoKabanetsWigderson2002]
-/

public section

namespace Cslib.Complexity.EasyWitness

open Circuits Circuits.Boolean Turing.MultiTapeTM Filter

/-- **A language in `PSPACE` that is hard at all large lengths**: for every `k`, some language in
`PSPACE` has slices that need more than `(n + 1) ^ k` gates for every large `n`. -/
theorem exists_mem_PSPACE_eventually_lt (k : ℕ) :
    ∃ L : Language Bool, (L : Set (List Bool)) ∈ PSPACE encBits ∧
      ∀ᶠ n in atTop, (n + 1) ^ k < complexity interpretation (single (L.slice n)) :=
  ⟨Kannan.language k, Kannan.language_mem_PSPACE k, Kannan.eventually_lt_complexity_slice k⟩

end Cslib.Complexity.EasyWitness
