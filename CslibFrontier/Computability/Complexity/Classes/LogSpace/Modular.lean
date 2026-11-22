/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.LogSpace.Counting
import CslibFrontier.Computability.Complexity.Classes.LogSpace.Hoza

/-!
# Modular counting in logarithmic space

For a fixed modulus `k`, `ModL k` consists of the languages recognized by a nonzero residue
modulo `k` of a `#L` count. It is the logarithmic-space analogue of `ModP`. The counts are those
of `SharpL`: one finite native counting machine, a logarithmic work-space bound on every
computation prefix, and transition occurrences counted with multiplicity. The modulus is a
class parameter, not part of the input. The definition is total in `k`; at `k = 1` it accepts no
instance.

At `k = 2` the condition is that the count is odd. This is `⊕L`, the languages accepted by an odd
number of accepting computation paths of a nondeterministic logspace machine, as defined by
[Reinhardt and Allender][ReinhardtAllender2000] in Section 1, page 3 of the version of March 31,
1999.

An unambiguous count is zero or one, so `UL ⊆ ModL k` for every `k ≥ 2`. Together with
`Cslib.Complexity.NL_eq_UL` this gives `NL ⊆ ModL k`, and in particular `NL ⊆ ⊕L`. On the same
page, Reinhardt and Allender attribute `NL/poly ⊆ ⊕L/poly` to Wigderson and describe `NL ⊆ ⊕L` as
not known to hold. The inclusion below is derived in this library from `NL = UL`; it is not
presented as the statement of a cited theorem.

## Main definitions

* `Cslib.Complexity.ModL`: nonzero residues of logspace accepting counts.

## Main results

* `Cslib.Complexity.NL_subset_ModL`: `NL ⊆ ModL k` for every `k ≥ 2` and every injective binary
  input encoding.

## References

* [K. Reinhardt, E. Allender, *Making Nondeterminism Unambiguous*][ReinhardtAllender2000]
* [W. M. Hoza, *NL = UL*][Hoza2026NLUL]
-/

public section

namespace Cslib.Complexity

variable {α : Type} {enc : α ↪ List Bool} {A : Set α} {k : ℕ}

/-- For a fixed modulus `k`, the languages recognized by a nonzero residue modulo `k` of a `#L`
count. The standard modular classes have `k ≥ 2`, and `ModL 2` is `⊕L`. -/
@[expose] def ModL (k : ℕ) (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ f ∈ SharpL enc, ∀ a, a ∈ A ↔ f a % k ≠ 0}

/-- Modulo two, a nonzero residue is an odd count, so `ModL 2` is `⊕L`
[Reinhardt and Allender, Section 1][ReinhardtAllender2000]. -/
theorem mem_ModL_two : A ∈ ModL 2 enc ↔ ∃ f ∈ SharpL enc, ∀ a, a ∈ A ↔ Odd (f a) := by
  simp only [ModL, Set.mem_ofPred_eq, Nat.odd_iff, Nat.mod_two_ne_zero]

/-- An unambiguous count is zero or one, so every modulus at least two recognizes it. -/
theorem UL_subset_ModL (hk : 2 ≤ k) : UL enc ⊆ ModL k enc := by
  rintro A ⟨f, hf, hle, hA⟩
  refine ⟨f, hf, fun a => ?_⟩
  have := hle a
  rw [hA a, Nat.mod_eq_of_lt (by omega)]
  omega

/-- **Nondeterministic logarithmic space is within `Mod_k L`** for every fixed `k ≥ 2`, and in
particular within `⊕L`. Hoza's `NL = UL` [Hoza2026NLUL] gives each language in `NL` a logspace
count that is one on members and zero on nonmembers, in the same encoding. -/
theorem NL_subset_ModL (hk : 2 ≤ k) : NL enc ⊆ ModL k enc :=
  (NL_eq_UL enc).subset.trans (UL_subset_ModL hk)

end Cslib.Complexity
