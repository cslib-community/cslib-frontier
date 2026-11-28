/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.EXP
public import CslibFrontier.Computability.Complexity.Classes.Space
import CslibFrontier.Computability.Complexity.Classes.Space.Nondeterministic.DeterministicTime
import CslibFrontier.Computability.Complexity.Classes.Space.Nondeterministic.Savitch
import CslibFrontier.Computability.Complexity.Classes.Space.Time
import CslibFrontier.Computability.Complexity.Classes.TimeSpace.Basic

/-!
# Exponential space

`Cslib.Complexity.EXPSPACE enc` is the union of the deterministic space classes
`Cslib.Complexity.DSPACE enc (2 ^ n ^ k)` over `k`, the space analogue of
`Cslib.Complexity.EXP` [Arora and Barak, Section 4.1][AroraBarak09],
[Sipser, Section 9.1][Sipser2013].

`PSPACE` is the union of the classes `DSPACE (n ^ k)`
(`Cslib.Complexity.mem_PSPACE_iff_exists_mem_DSPACE`), and time bounds space
(`Cslib.Complexity.DTIME_subset_DSPACE`), so `PSPACE ⊆ EXPSPACE` and `EXP ⊆ EXPSPACE`. The first
inclusion is strict for problems on bit words by the space hierarchy theorem
(`Cslib.Complexity.PSPACE_ssubset_EXPSPACE`, in `Classes.EXPSPACE.Separation`). Nondeterministic
time also bounds nondeterministic space (`Cslib.Complexity.NTIME_subset_NSPACE`), and Savitch's
theorem squares the space bound (`Cslib.Complexity.NSPACE_subset_DSPACE_sq`), so
`NEXP ⊆ EXPSPACE`.

## Main definitions

* `Cslib.Complexity.EXPSPACE`: deterministic exponential space.

## Main results

* `Cslib.Complexity.mem_EXPSPACE_iff`: membership is membership in some `DSPACE (2 ^ n ^ k)`.
* `Cslib.Complexity.DSPACE_two_pow_subset_EXPSPACE`: space `2 ^ h n` for a polynomially bounded
  `h` is exponential space.
* `Cslib.Complexity.PSPACE_subset_EXPSPACE`: polynomial space is within exponential space.
* `Cslib.Complexity.EXP_subset_EXPSPACE`: exponential time is within exponential space.
* `Cslib.Complexity.NEXP_subset_EXPSPACE`: nondeterministic exponential time is within
  exponential space.
* `Cslib.Complexity.compl_mem_EXPSPACE`: closure under complement.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
* [W. J. Savitch, *Relationships between nondeterministic and deterministic tape
  complexities*][Savitch1970]
-/

@[expose] public section

namespace Cslib.Complexity

variable {α : Type*} {enc : α ↪ List Bool} {A : Set α}

/-- The problems decidable within space `O(2 ^ n ^ k)` for some `k`, on instances whose encoding
under `enc` has length `n` [Arora and Barak, Section 4.1][AroraBarak09]. -/
def EXPSPACE (enc : α ↪ List Bool) : Set (Set α) := ⋃ k, DSPACE enc fun n => 2 ^ n ^ k

theorem mem_EXPSPACE_iff : A ∈ EXPSPACE enc ↔ ∃ k, A ∈ DSPACE enc fun n => 2 ^ n ^ k :=
  Set.mem_iUnion

/-- Deterministic space `2 ^ h n`, for a polynomially bounded exponent `h`, is within exponential
space. -/
theorem DSPACE_two_pow_subset_EXPSPACE {h : ℕ → ℕ} (hh : PolynomiallyBounded h) :
    DSPACE enc (fun n => 2 ^ h n) ⊆ EXPSPACE enc := fun _ hA =>
  let ⟨k, hk⟩ := hh
  mem_EXPSPACE_iff.mpr ⟨k, DSPACE_mono_of_eventually_le
    (hk.mono fun _ hn => Nat.pow_le_pow_right (by norm_num) hn) hA⟩

/-- **Polynomial space is within exponential space**: `n ^ k < 2 ^ n ^ k`. -/
theorem PSPACE_subset_EXPSPACE {α : Type} {enc : α ↪ List Bool} :
    PSPACE enc ⊆ EXPSPACE enc := fun _ hA =>
  let ⟨k, hk⟩ := mem_PSPACE_iff_exists_mem_DSPACE.mp hA
  mem_EXPSPACE_iff.mpr ⟨k, DSPACE_mono (fun n => (Nat.lt_two_pow_self (n := n ^ k)).le) hk⟩

/-- **Exponential time is within exponential space**: time bounds space
(`Cslib.Complexity.DTIME_subset_DSPACE`). -/
theorem EXP_subset_EXPSPACE : EXP enc ⊆ EXPSPACE enc := fun _ hA =>
  let ⟨k, hk⟩ := mem_EXP_iff.mp hA
  mem_EXPSPACE_iff.mpr ⟨k, DTIME_subset_DSPACE hk⟩

/-- **Nondeterministic exponential time is within exponential space**: a problem in
`NTIME (2 ^ n ^ k)` is in `NSPACE (2 ^ (n ^ k + n))` (`Cslib.Complexity.NTIME_subset_NSPACE`), a
bound above `log₂ n`, so Savitch's theorem [Savitch1970] places it in
`DSPACE (2 ^ ((n ^ k + n) * 2))` (`Cslib.Complexity.NSPACE_subset_DSPACE_sq`). -/
theorem NEXP_subset_EXPSPACE {α : Type} {enc : α ↪ List Bool} : NEXP enc ⊆ EXPSPACE enc := by
  intro A hA
  obtain ⟨k, hk⟩ := mem_NEXP_iff.mp hA
  have h := NSPACE_subset_DSPACE_sq (s := fun n => 2 ^ (n ^ k + n))
    (fun n => (Nat.log2_le_self n).trans (Nat.lt_two_pow_self.le.trans
      (Nat.pow_le_pow_right (by norm_num) (Nat.le_add_left n _))))
    (NSPACE_mono (fun n => Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right _ n))
      (NTIME_subset_NSPACE hk))
  simp only [← pow_mul] at h
  exact DSPACE_two_pow_subset_EXPSPACE (by fun_prop) h

/-- `EXPSPACE` is closed under complement (`Cslib.Complexity.compl_mem_DSPACE`). -/
theorem compl_mem_EXPSPACE {α : Type} {enc : α ↪ List Bool} {A : Set α} (h : A ∈ EXPSPACE enc) :
    Aᶜ ∈ EXPSPACE enc :=
  let ⟨k, hk⟩ := mem_EXPSPACE_iff.mp h
  mem_EXPSPACE_iff.mpr ⟨k, compl_mem_DSPACE hk⟩

end Cslib.Complexity
