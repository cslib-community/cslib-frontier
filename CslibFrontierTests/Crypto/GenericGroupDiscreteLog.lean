/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.GenericGroup.DiscreteLog

/-!
# The generic-group bound for discrete logarithm: an ordinary client

Uses the public API of `CslibFrontier.Crypto.Computational.GenericGroup.Relabel` and
`CslibFrontier.Crypto.Computational.GenericGroup.DiscreteLog` through ordinary imports:

* the sharp bound for the adversary of `ZMod 5` that makes no query and guesses `1` when its two
  labels agree: success probability at most `2 / 5`;
* the book's form for any query-bounded adversary, and the query bound of a relabelled program;
* `Nonempty (ZMod q ↪ S)` is the book's `|S| ≥ q`;
* primality is needed where the proof uses it: in `ZMod 4` the distinct linear forms `2 X` and `0`
  agree at two points.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.GenericGroupDiscreteLog

open Cslib Cslib.Crypto.GenericGroup
open scoped NNReal

/-! ### An adversary without queries -/

/-- Guess `1` when the generator and the challenge have the same label, `0` otherwise; no query. -/
private def guess (g u : ZMod 5) : ProbOracleComp (GroupOracleSpec 5 (ZMod 5)) (ZMod 5) :=
  pure (if g = u then 1 else 0)

private instance : Nonempty (ZMod 5 ↪ ZMod 5) := ⟨Function.Embedding.refl _⟩

example : (dlogGame guess).succProbability ≤ 2 / 5 := by
  refine (succProbability_dlogGame_le_choose (T := 0) Nat.prime_five
    fun g u => OracleComp.IsCostBounded.pure _ 0).trans_eq ?_
  norm_num [Nat.choose_self]

/-! ### The book's form and relabelling -/

example {q : ℕ} [NeZero q] {S : Type} [Fintype S] [Nonempty (ZMod q ↪ S)] (hq : q.Prime)
    {T : ℕ} {A : S → S → ProbOracleComp (GroupOracleSpec q S) (ZMod q)}
    (hA : ∀ g u, (A g u).IsQueryBounded T) :
    (dlogGame A).succProbability ≤ ((3 * T + 2 : ℝ≥0) ^ 2 / 2 + 1) / q :=
  succProbability_dlogGame_le hq hA

example {q : ℕ} {S : Type} (j : ZMod q ↪ S) {T : ℕ}
    {A : ProbOracleComp (GroupOracleSpec q S) (ZMod q)} (hA : A.IsQueryBounded T) :
    (relabel j A).IsQueryBounded T :=
  isQueryBounded_relabel j hA

/-! ### Hypotheses -/

/-- An injective labeling exists exactly when `S` has at least `q` elements. -/
example (q : ℕ) [NeZero q] {S : Type} [Fintype S] : Nonempty (ZMod q ↪ S) ↔ q ≤ Fintype.card S := by
  rw [Function.Embedding.nonempty_iff_card_le, ZMod.card]

/-- Over `ZMod 4` the distinct forms `2 X + 0` and `0 X + 0` agree at `0` and `2`; the proof of
the bound needs `q` prime exactly here. -/
example : (Finset.univ.filter fun α : ZMod 4 => 2 * α + 0 = 0 * α + 0).card = 2 := by
  decide

end CslibFrontierTests.Crypto.GenericGroupDiscreteLog
