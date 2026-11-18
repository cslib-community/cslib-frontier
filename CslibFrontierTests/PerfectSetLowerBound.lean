/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Complexity.Classes.ArthurMerlin.SetLowerBound

/-! A satisfying instance of the perfectly complete set lower bound protocol
([Arora and Barak, Exercise 8.3][AroraBarak07]): every binary string is a member, the certified
set is the single empty string with the empty certificate, and the threshold is `1`. -/

set_option linter.privateModule false

namespace CslibFrontierTests.PerfectSetLowerBound

open Cslib Cslib.Complexity Finset Turing.MultiTapeTM

/-- The certified set of the always-accepting test, with no bits and no certificate, has one
element, so the hypotheses hold with `K = 1` for the problem of all strings. -/
example : ∃ (p q : Polynomial ℕ) (V : List Bool × List Bool → Bool),
    ComputableInPolyTime V (encPair encBits encBits) encBool ∧
    ∀ a, (a ∈ (Set.univ : Set (List Bool)) → ∀ r : Fin (p.eval (encBits a).length) → Bool,
        ∃ y : Fin (q.eval (encBits a).length) → Bool, V (a, List.ofFn r ++ List.ofFn y) = true) ∧
      (a ∉ (Set.univ : Set (List Bool)) → 3 * #{r : Fin (p.eval (encBits a).length) → Bool |
        ∃ y : Fin (q.eval (encBits a).length) → Bool,
          V (a, List.ofFn r ++ List.ofFn y) = true} ≤ 2 ^ p.eval (encBits a).length) :=
  exists_perfectlyComplete_verifier_of_card_certifiedSet (N := 0) (c := 0)
    (R := fun _ => true) (K := fun _ => 1) (.const _) (.const _) (fun _ => one_pos)
    (fun _ _ => card_pos.2 ⟨fun _ => false,
      mem_filter.2 ⟨mem_univ _, fun _ => false, rfl⟩⟩)
    (fun a ha => absurd (Set.mem_univ a) ha)

end CslibFrontierTests.PerfectSetLowerBound
