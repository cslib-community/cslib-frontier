/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Set.Finite.List
import CslibFrontier.Foundations.Data.BitString.ShortWords

/-!
# Binary words of one length

## Main definitions

* `Cslib.BitString.wordsOfLength`: the `Finset` of binary words of length `n`.

## Main results

* `Cslib.BitString.mem_wordsOfLength`: its members are the words of length `n`.
* `Cslib.BitString.card_wordsOfLength`: it has `2 ^ n` members.
-/

public section

namespace Cslib.BitString

/-- The binary words of length `n`. -/
noncomputable def wordsOfLength (n : ℕ) : Finset (List Bool) :=
  (List.finite_length_eq Bool n).toFinset

/-- A word lies in `wordsOfLength n` exactly when its length is `n`. -/
@[simp]
theorem mem_wordsOfLength {n : ℕ} {w : List Bool} : w ∈ wordsOfLength n ↔ w.length = n := by
  simp [wordsOfLength]

/-- There are `2 ^ n` binary words of length `n`. -/
theorem card_wordsOfLength (n : ℕ) : (wordsOfLength n).card = 2 ^ n := by
  have h := (List.finite_length_eq Bool n).encard_eq_coe_toFinset_card
  rw [encard_setOf_length_eq] at h
  exact_mod_cast h.symm

end Cslib.BitString
