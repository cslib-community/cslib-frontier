/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Complexity.Classes.ArthurMerlin.Derandomization

/-! Checked client of Arora and Barak's Exercise 16.4
(`Cslib.Complexity.MA_eq_NP_of_isAverageCaseHard`). -/

set_option linter.privateModule false

open Filter Cslib Cslib.Circuits.Boolean Cslib.Complexity Turing.MultiTapeTM

/-- Under the hardness hypothesis, `MA` and `NP` agree on problems about words, and both contain
`BPP`. -/
example {L : Language Bool} {c : ℕ} (hL : (L : Set (List Bool)) ∈ E encBits) (hc : 0 < c)
    (hard : ∀ᶠ n in atTop, IsAverageCaseHard (L.slice n) (2 ^ (n / c))) :
    MA encBits = NP encBits ∧ BPP encBits ⊆ NP encBits := by
  have hMA := MA_eq_NP_of_isAverageCaseHard hL hc hard encBits
  exact ⟨hMA, hMA ▸ BPP_subset_MA⟩
