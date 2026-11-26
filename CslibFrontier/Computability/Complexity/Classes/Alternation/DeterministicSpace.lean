/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Alternation
public import CslibFrontier.Computability.Complexity.Classes.Space.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.DeterministicSpace

/-!
# Alternating time within deterministic space

An alternating machine deciding a problem within time `t` is evaluated depth first: the
deterministic machine keeps the moves made so far and replays them on the alternating machine to
learn whether the position is a leaf, which player moves and whether it is won
(`Turing.MultiTapeATM.computableInSpace_gameValue`). In this implementation, replaying moves copies
the encoded input of length `n` to a work tape, giving the library's general formulation
`ATIME t ⊆ DSPACE (n + t n)` for arbitrary `t : ℕ → ℕ` (`Cslib.Complexity.ATIME_subset_DSPACE`).
When `∀ n, n ≤ t n`, this specializes to `ATIME t ⊆ DSPACE t`
(`Cslib.Complexity.ATIME_subset_DSPACE_of_le`), matching Theorem 3.2 of
[Chandra, Kozen and Stockmeyer][ChandraKozenStockmeyer1981] (printed pp. 122–123; see also
[Sipser, Section 10.3][Sipser2013]) in the library's binary halting-decider model.

Chandra, Kozen and Stockmeyer (Definition 2.5 and Theorem 3.2, pp. 120 and 122–123) define
`ATIME(T(n))` and `DSPACE(T(n))` over arbitrary finite alphabets via least-fixed-point recognizers,
so their proof removes constructibility of `T(n)` on p. 123 by trying depths `T = 1, 2, …` in turn
(which can continue trying larger depths on rejected inputs). Here `ATIME enc t`
(`Turing.MultiTapeATM.DecidesInTime`) and `DSPACE enc s`
(`Turing.MultiTapeTM.DecidableInTimeAndSpace`) use binary-alphabet halting deciders up to linear
factors `c₁ * t n + c₂` and `c₁ * s n + c₂`, as in Sipser: every computation path of an
`ATIME enc t` decider halts within `c₁ * t n + c₂` moves, so the depth-first evaluator halts on
every input without computing `t`. On printed pp. 123–124, Chandra, Kozen and Stockmeyer remark
that equipping alternating machines with random-access input indexing suffices in their proof to
avoid writing the entire input in each reconstructed configuration and relax `T(n) ≥ n` to
`T(n) ≥ log n` (without claiming random access is necessary for the inclusion); in the sequential
replay implementation here, the `n` term in `ATIME_subset_DSPACE` pays for the input copy.

## Main results

* `Cslib.Complexity.ATIME_subset_DSPACE`: `ATIME t ⊆ DSPACE (n + t n)` for arbitrary `t`.
* `Cslib.Complexity.ATIME_subset_DSPACE_of_le`: `ATIME t ⊆ DSPACE t` when `n ≤ t n`.

## References

* [A. K. Chandra, D. C. Kozen, L. J. Stockmeyer, *Alternation*,
  Theorem 3.2][ChandraKozenStockmeyer1981]
* [M. Sipser, *Introduction to the Theory of Computation*, Section 10.3][Sipser2013]
-/

public section

namespace Cslib.Complexity

open Turing Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}

/-- **Alternating time is within deterministic space `O(n + t n)`**: the library's formulation for
arbitrary `t : ℕ → ℕ`, `ATIME t ⊆ DSPACE (n + t n)`, with no constructibility hypothesis on `t`,
where `n` pays for copying the encoded input during sequential coin replay (specializing to
[Chandra, Kozen and Stockmeyer, Theorem 3.2][ChandraKozenStockmeyer1981] under `n ≤ t n` in
`ATIME_subset_DSPACE_of_le`). -/
theorem ATIME_subset_DSPACE {t : ℕ → ℕ} : ATIME enc t ⊆ DSPACE enc fun n => n + t n := by
  rintro A ⟨c₁, c₂, k, State, _, atm, hA⟩
  obtain ⟨T, c, h, -⟩ := atm.computableInSpace_gameValue fun a => (hA a).1
  have hind : (fun a => atm.gameValue (enc a) (c₁ * t (enc a).length + c₂) []) =
      MultiTapeTM.indicator A := by
    funext a
    by_cases ha : a ∈ A <;>
      simp [MultiTapeTM.indicator, ha, ← hA.mem_iff_gameValue, Bool.eq_false_iff]
  rw [hind] at h
  refine mem_DSPACE_iff.mpr ⟨c * (c₁ + 1), c * (c₂ + 1), T, h.mono (fun _ => le_rfl) fun a => ?_⟩
  nlinarith [Nat.zero_le (c * c₁ * (enc a).length), Nat.zero_le (c * t (enc a).length)]

/-- **Alternating time within deterministic space, for `t n ≥ n`** [Chandra, Kozen and Stockmeyer,
Theorem 3.2][ChandraKozenStockmeyer1981]: `ATIME t ⊆ DSPACE t` when `∀ n, n ≤ t n`, in the
library's binary halting-decider model, with no constructibility hypothesis on `t`. -/
theorem ATIME_subset_DSPACE_of_le {t : ℕ → ℕ} (ht : ∀ n, n ≤ t n) :
    ATIME enc t ⊆ DSPACE enc t :=
  ATIME_subset_DSPACE.trans (DSPACE_mono_of_le_mul_add (C := 2) fun n => by have := ht n; omega)

end Cslib.Complexity
