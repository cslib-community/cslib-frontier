/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Foundations.Data.List.LengthCounting
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.NormNum

/-!
# Bounded-multiplicity list counting

The family contains two copies each of the words of lengths zero, one and two over a
one-letter alphabet. The length lower bound applies although its map to words is not
injective. Empty families and threshold zero exercise the natural-subtraction boundaries.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.ListLengthCounting

private def family : Finset (List Unit × Bool) :=
  ({[], [()], [(), ()]} : Finset (List Unit)) ×ˢ Finset.univ

example : ¬ Set.InjOn (Prod.fst : List Unit × Bool → List Unit) (family : Set _) := by
  intro h
  have heq := h (x₁ := ([], false)) (by simp [family])
    (x₂ := ([], true)) (by simp [family]) rfl
  exact Bool.false_ne_true (congrArg Prod.snd heq)

/-- A noninjective family still has a positive length lower bound at multiplicity two. -/
example : 2 ≤ ∑ p ∈ family, p.1.length := by
  have hf (l : List Unit) : (family.filter fun p => p.1 = l).card ≤ 2 := by
    calc _ ≤ (Finset.univ : Finset Bool).card :=
          Finset.card_le_card_of_injOn (fun p => p.2) (fun _ _ => Finset.mem_univ _)
            (fun p hp q hq heq => Prod.ext
              ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm) heq)
      _ = 2 := by decide
  have h := Finset.card_sub_mul_pow_mul_le_sum_length hf 1
  simpa [family] using h

/-- A zero multiplicity bound is possible for the empty family. -/
example : (0 - 0 * (Fintype.card Unit + 1) ^ 3) * 3 ≤
    ∑ p ∈ (∅ : Finset (List Unit)), p.length :=
  Finset.card_sub_mul_pow_mul_le_sum_length (s := ∅) (f := id) (M := 0)
    (by intro l; simp) 3

/-- The length threshold may be zero for a nonempty injective family. -/
example : (({[()]} : Finset (List Unit)).card - (Fintype.card Unit + 1) ^ 0) * 0 ≤
    ∑ l ∈ ({[()]} : Finset (List Unit)), l.length :=
  Finset.card_sub_pow_mul_le_sum_length (f := id) (fun _ _ _ _ h => h) 0

end CslibFrontierTests.ListLengthCounting
