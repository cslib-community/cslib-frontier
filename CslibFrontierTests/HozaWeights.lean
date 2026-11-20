/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Algorithms.Reachability.MinIsolation.Collisions

/-! # Hoza's base-six weights and collision bound -/

set_option linter.privateModule false

namespace CslibFrontierTests.HozaWeights

open Cslib.Reachability.Hoza

-- On layer 4, the first of two bits has coefficient 6³ and the second 6².
private theorem valuation_four : padicValNat 2 4 = 2 := by
  change (Nat.maxPowDvdDiv 2 4).1 = 2
  rw [Nat.maxPowDvdDiv_of_pow_mul_eq (by decide) (show 2 ^ 2 * 1 = 4 by decide) (by decide)]

example : coefficient 4 (0 : Fin 2) = 216 := by
  rw [coefficient, valuation_four]
  decide

example : coefficient 4 (1 : Fin 2) = 36 := by
  rw [coefficient, valuation_four]
  decide

example : vertexWeight (ℓ := 2) (fun (_ : Unit) _ => true) (fun _ => true) 0 () = 0 := rfl

open Finset in
-- In a one-layer interval, two complementary codewords can tie for at most one seed.
example :
    let layers := Icc 1 1
    let code (v : Bool) (_ : Fin 2) := v
    let column (v : Bool) (_ : ℕ) := v
    let f seed := minIntervalWeight code seed layers column {false} (singleton_nonempty _)
    let g seed := minIntervalWeight code seed layers column {true} (singleton_nonempty _)
    (univ.filter fun seed => f seed = g seed).card ≤ 1 := by
  intro layers code column f g
  have hmax : ∀ i ∈ layers, multiplicity 2 i ≤ multiplicity 2 1 := by
    intro i hi
    have hi' : i = 1 := by simpa [layers] using hi
    subst i
    rfl
  have h := card_tyingSeeds_le code (by decide) (by decide) hmax column
    (singleton_nonempty false) (singleton_nonempty true) false true
    (fun p hp => mem_singleton.mp hp) (fun p hp => mem_singleton.mp hp)
  simpa [f, g, layers, show hammingDist (code false) (code true) = 2 by decide] using h

end CslibFrontierTests.HozaWeights
