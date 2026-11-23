/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.BinarySlice
import Mathlib.Tactic.FinCases

/-!
# Binary slice boundary witnesses

Fixed native machines handle empty inputs, exact boundaries, zero-length element payloads and
binary indices far larger than the stored words.
-/

public section

namespace Turing.MultiTapeTM.BinarySlice.Tests

/-- Empty, interior, boundary and oversized-index bit queries. -/
def bitRequests : Fin 6 → (List Bool × ℕ) × Bool := ![
  (([], 0), false),
  (([true, false, true], 0), true),
  (([true, false, true], 1), false),
  (([true, false, true], 2), true),
  (([true, false, true], 3), false),
  (([true, false, true], 2 ^ 100), false)]

-- A single native machine handles empty words, both bit values, the exact boundary and a
-- very large binary index. The full word is charged only linearly in its time and space.
/-- The bit-boundary cases share one finite native machine. -/
theorem native_bit_boundaries :
    ∃ (d c K : ℕ) (Q : Type) (_ : Finite Q) (tm : MultiTapeTM K Bool Q), ∀ i,
    let a := (bitRequests i).1
    let budget := c * (a.1.length + (a.1.length.size + a.2.size + 1) ^ d + 1)
    tm.ComputesInTimeAndSpace (encPair encBits encNat a) (encBool (bitRequests i).2)
      budget budget := by
  obtain ⟨d, c, ⟨K, Q, hQ, tm, htm⟩, _⟩ := ComputableInO.exists_bitsGetD_binary
  refine ⟨d, c, K, Q, hQ, tm, fun i => ?_⟩
  have h : (bitRequests i).1.1.getD (bitRequests i).1.2 false = (bitRequests i).2 := by
    fin_cases i <;> decide
  simpa only [h] using htm (bitRequests i).1

private def listRequests : Fin 7 → (List ℕ × (ℕ × ℕ)) × List ℕ := ![
  (([], (0, 2)), []),
  (([0, 3, 0, 7], (1, 2)), [3, 0]),
  (([0, 3, 0, 7], (0, 0)), []),
  (([0, 3, 0, 7], (2, 20)), [0, 7]),
  (([0, 3, 0, 7], (4, 1)), []),
  (([0, 3, 0, 7], (2 ^ 100, 1)), []),
  (([0, 3, 0, 7], (1, 2 ^ 100)), [3, 0, 7])]

-- Framed elements include zero, whose binary payload is empty. Capping must preserve
-- element boundaries while also avoiding expansion of the two huge binary indices.
example : ∃ (d c K : ℕ) (Q : Type) (_ : Finite Q) (tm : MultiTapeTM K Bool Q), ∀ i,
    let a := (listRequests i).1
    let n := (encList encNat a.1).length
    let budget := c * (n + (n.size + a.2.1.size + a.2.2.size + 1) ^ d + 1)
    tm.ComputesInTimeAndSpace (encPair (encList encNat) (encPair encNat encNat) a)
      (encList encNat (listRequests i).2) budget budget := by
  obtain ⟨d, c, ⟨K, Q, hQ, tm, htm⟩, _⟩ := ComputableInO.exists_listSlice_binary encNat
  refine ⟨d, c, K, Q, hQ, tm, fun i => ?_⟩
  have h : ((listRequests i).1.1.drop (listRequests i).1.2.1).take
      (listRequests i).1.2.2 = (listRequests i).2 := by
    fin_cases i <;> decide
  simpa only [h] using htm (listRequests i).1

end Turing.MultiTapeTM.BinarySlice.Tests
