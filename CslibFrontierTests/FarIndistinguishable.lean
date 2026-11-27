/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Crypto.Computational.FarIndistinguishable

/-! Checked clients for [Goldreich2007DraftR4], Exercises 8.7 and 8.8. Statistical distance at
least `1 / 2` gives the draft's "statistically far apart" (Exercise 8.9: variation distance greater
than `1 / p(n)`) with `p = 3` at every `n`. The one-to-one hypothesis of the exact-`1 / 2` lemma
holds for the identity, and then the distance is exactly `1 / 2` whatever the appended bit. -/

set_option linter.privateModule false

namespace CslibFrontierTests.FarIndistinguishable

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM
open scoped ENNReal

/-- Distance at least `1 / 2` excludes distance at most `1 / 3`. -/
theorem not_closeTo_third {μ ν : PMF (List Bool)} (h : ∀ ε, CloseTo μ ν ε → 1 / 2 ≤ ε) :
    ¬ CloseTo μ ν (1 / 3) := fun hclose => by
  exact (h _ hclose).not_gt
    (ENNReal.div_lt_div_left one_ne_zero ENNReal.one_ne_top (by norm_num))

-- Exercise 8.7 in the draft's "statistically far apart" form, with `p(n) = 3`.
example {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (h : PseudorandomGenerator generator length) :
    ∃ X Y : ℕ → ProbComp (List Bool), IsPPTOn encUnary encBits X ∧ IsPPTOn encUnary encBits Y ∧
      ComputationallyIndistinguishable (fun n => ProbComp.eval (X n))
        (fun n => ProbComp.eval (Y n)) ∧
      ∀ n, ¬ CloseTo (ProbComp.eval (X n)) (ProbComp.eval (Y n)) (1 / 3) := by
  obtain ⟨X, Y, hX, hY, hind, hfar⟩ := h.exists_far_indistinguishable
  exact ⟨X, Y, hX, hY, hind, fun n => not_closeTo_third (hfar n)⟩

-- Exercise 8.8 in the same form.
example {f : List Bool → List Bool} (hf : OneWay f) (hinj : Function.Injective f) :
    ∃ X Y : ℕ → ProbComp (List Bool), IsPPTOn encUnary encBits X ∧ IsPPTOn encUnary encBits Y ∧
      ComputationallyIndistinguishable (fun n => ProbComp.eval (X n))
        (fun n => ProbComp.eval (Y n)) ∧
      ∀ n, ¬ CloseTo (ProbComp.eval (X n)) (ProbComp.eval (Y n)) (1 / 3) := by
  obtain ⟨X, Y, hX, hY, hind, hfar⟩ := hf.exists_far_indistinguishable_of_injective hinj
  exact ⟨X, Y, hX, hY, hind, fun n => not_closeTo_third fun ε => (hfar n ε).1⟩

-- The one-to-one hypothesis is satisfiable: for the identity and a constant bit, the distance is
-- exactly `1 / 2` at every length.
example (n : ℕ) (ε : ℝ≥0∞) :
    CloseTo (generatorEnsemble (fun seed => id seed ++ [true]) n) (hardCoreIdeal id n) ε ↔
      1 / 2 ≤ ε :=
  closeTo_generatorEnsemble_hardCoreIdeal_iff (fun _ => true) (Set.injOn_id _)

end CslibFrontierTests.FarIndistinguishable
