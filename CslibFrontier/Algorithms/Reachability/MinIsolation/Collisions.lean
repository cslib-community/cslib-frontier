/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Reachability.MinIsolation.Weights
public import Mathlib.InformationTheory.Hamming

/-!
# Collisions between Hoza's minimum path weights

Fix an interval and its dominant layer. Consider two nonempty path families
whose columns at the dominant layer are fixed. Any seed tying their minimum
weights is determined by its restriction to the coordinates on which the two
columns' codewords agree [Hoza2026NLUL, Theorem 2.4].

## Main results

* `Cslib.Reachability.Hoza.card_tyingSeeds_le` bounds the number of tying seeds by
  two raised to the number of agreeing codeword coordinates.
-/

public section

namespace Cslib.Reachability.Hoza

open Finset Function

variable {ℓ : ℕ}

/-- For two path families with fixed columns at the dominant layer, the number of seeds
that tie their minimum weights is at most two to the number of agreeing codeword bits. -/
theorem card_tyingSeeds_le {V P : Type*} (code : V → Fin ℓ → Bool)
    {a b mid : ℕ} (ha : 0 < a) (hm : mid ∈ Icc a b)
    (hmax : ∀ i ∈ Icc a b, multiplicity 2 i ≤ multiplicity 2 mid)
    (column : P → ℕ → V) {paths₁ paths₂ : Finset P}
    (hne₁ : paths₁.Nonempty) (hne₂ : paths₂.Nonempty)
    (u v : V) (hu : ∀ p ∈ paths₁, column p mid = u)
    (hv : ∀ p ∈ paths₂, column p mid = v) :
    let f seed := minIntervalWeight code seed (Icc a b) column paths₁ hne₁
    let g seed := minIntervalWeight code seed (Icc a b) column paths₂ hne₂
    (univ.filter fun seed => f seed = g seed).card ≤ 2 ^ (ℓ - hammingDist (code u) (code v)) :=
  MinIsolation.BaseSix.card_tyingSeeds_le_of_update_bounds
    (fun seed => minIntervalWeight code seed (Icc a b) column paths₁ hne₁)
    (fun seed => minIntervalWeight code seed (Icc a b) column paths₂ hne₂)
    (m := padicValNat 2 mid)
    (fun seed j => minIntervalWeight_update_bounds code seed ha hm hmax column hne₁ u hu j)
    (fun seed j => minIntervalWeight_update_bounds code seed ha hm hmax column hne₂ v hv j)

end Cslib.Reachability.Hoza
