/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.LogSpace.Counting

/-!
# Modular counting in logarithmic space

For a fixed modulus `k`, `ModL k` consists of the languages recognized by a nonzero residue
modulo `k` of a `#L` count. It is the logarithmic-space analogue of `ModP`. The counts are those
of `SharpL`: one finite native counting machine, a logarithmic work-space bound on every
computation prefix, and transition occurrences counted with multiplicity. The modulus is a
class parameter, not part of the input. The definition is total in `k`; at `k = 1` it accepts no
instance.

At `k = 2` the condition is that the count is odd. This is the library's parity-count form of
`⊕L`. [Reinhardt and Allender][ReinhardtAllender2000] define `⊕L` by an odd number of accepting
computation paths of a nondeterministic logspace machine (Section 1, page 3 of the version of
March 31, 1999). The library does not prove that counting transition occurrences of a native
counting machine gives the same class as counting paths.

An unambiguous count is zero or one, so `UL ⊆ ModL k` for every `k ≥ 2`. The inclusion of `NL`
in these classes is `Cslib.Complexity.NL_subset_ModL`, stated beside `NL = UL`.

## Main definitions

* `Cslib.Complexity.ModL`: nonzero residues of logspace accepting counts.

## Main results

* `Cslib.Complexity.mem_ModL_two`: modulo two, membership is oddness of the count.
* `Cslib.Complexity.UL_subset_ModL`: `UL ⊆ ModL k` for every `k ≥ 2`.

## References

* [K. Reinhardt, E. Allender, *Making Nondeterminism Unambiguous*][ReinhardtAllender2000]
-/

public section

namespace Cslib.Complexity

variable {α : Type} {enc : α ↪ List Bool} {A : Set α} {k : ℕ}

/-- For a fixed modulus `k`, the languages recognized by a nonzero residue modulo `k` of a `#L`
count. The standard modular classes have `k ≥ 2`, and `ModL 2` is the library's parity-count form
of `⊕L`. -/
@[expose] def ModL (k : ℕ) (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ f ∈ SharpL enc, ∀ a, a ∈ A ↔ f a % k ≠ 0}

/-- Modulo two, a nonzero residue is an odd count: the parity-count condition defining `⊕L` in
[Reinhardt and Allender, Section 1][ReinhardtAllender2000], for the library's occurrence
counts. -/
theorem mem_ModL_two : A ∈ ModL 2 enc ↔ ∃ f ∈ SharpL enc, ∀ a, a ∈ A ↔ Odd (f a) := by
  simp only [ModL, Set.mem_ofPred_eq, Nat.odd_iff, Nat.mod_two_ne_zero]

/-- An unambiguous count is zero or one, so every modulus at least two recognizes it. -/
theorem UL_subset_ModL (hk : 2 ≤ k) : UL enc ⊆ ModL k enc := by
  rintro A ⟨f, hf, hle, hA⟩
  refine ⟨f, hf, fun a => ?_⟩
  have := hle a
  rw [hA a, Nat.mod_eq_of_lt (by omega)]
  omega

end Cslib.Complexity
