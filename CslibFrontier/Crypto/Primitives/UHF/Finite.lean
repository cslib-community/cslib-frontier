/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Basic
public import CslibFrontier.Probability.HashFamily
import CslibFrontier.Languages.Probabilistic.Semantics
import CslibFrontier.Probability.HashFamily.Collisions
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.UniformPoint

/-!
# Multi-query universal hash games on finite types

This module formalizes only the multi-query universal-hash game
(`Cslib.Crypto.UHF.multiQueryExperiment`, Attack Game 7.2 of [BonehShoup2023], Section 7.1.1,
p. 254) for finite key types and the collision union bound for an `ε`-bounded UHF
(`Cslib.Crypto.UHF.eval_multiQueryExperiment_le`, the `ε`-bounded case of Lemma 7.1).

Attack Game 7.1 (`UHFadv`), computational UHFs (Definition 7.2), multi-query UHFs against
efficient adversaries (Definition 7.3), the difference-unpredictability game (Attack Game 7.3), and
the computational reduction of Lemma 7.1 are not formalized here. No running-time certificate is
attached to the adversary `B`: it is an arbitrary closed probabilistic program outputting a finite
list of messages.

## Main definitions

* `Cslib.Crypto.UHF.multiQueryExperiment`: Attack Game 7.2 (multi-query UHF) on finite types.

## Main results

* `Cslib.Crypto.UHF.eval_multiQueryExperiment_le`: `C(Q, 2) * ε` bound on winning Attack Game 7.2
  with lists of at most `Q` messages against an `ε`-bounded UHF.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 7.1.1, Attack Game 7.2 and Lemma 7.1, p. 254.
-/

public section

namespace Cslib.Crypto.UHF

open Cslib.Probability
open scoped ENNReal

variable {K M Y : Type}

/-- Attack Game 7.2 (multi-query UHF, [BonehShoup2023], Version 0.6, Section 7.1.1, p. 254): the
adversary `B` outputs a list of messages, the challenger samples a uniform hash key independently,
and `B` wins when two distinct messages of the list have the same digest (`MUHFadv[B, H]` is the
probability of `true`). The book asks `B` to output distinct messages; Lean accepts any `List M`
and rewards only pairs with `m ≠ m'` and `H k m = H k m'`, so duplicate messages earn nothing. -/
@[expose] noncomputable def multiQueryExperiment [Fintype K] [Nonempty K] [DecidableEq M]
    [DecidableEq Y] (H : K → M → Y) (B : ProbComp (List M)) : ProbComp Bool := do
  let ms ← B
  let k ← ProbComp.uniform K
  return decide (∃ m ∈ ms, ∃ m' ∈ ms, m ≠ m' ∧ H k m = H k m')

/-- The `ε`-bounded case of [BonehShoup2023], Lemma 7.1, a step toward the lemma, not the cited
result: against an `ε`-bounded UHF (`IsUniversalHash` for the uniform key, the `ε`-UHF of
Definition 7.2), an adversary whose supported output lists have length at most `Q` wins Attack
Game 7.2 with probability at most `Q.choose 2 * ε`. Only the key type has to be finite. Lemma 7.1
assumes only a computational UHF and bounds the multi-query advantage by `Q ^ 2 / 2` times the
advantage of an efficient wrapper in Attack Game 7.1; here the hash is `ε`-bounded against every
adversary, efficient or not, for one fixed instance, with any `ε` (Definition 7.2 calls it
statistical only when `ε` is negligible), and no wrapper is built (#5790). -/
theorem eval_multiQueryExperiment_le [Fintype K] [Nonempty K] [DecidableEq M] [DecidableEq Y]
    {H : K → M → Y} {ε : ℝ≥0∞} (hH : IsUniversalHash (PMF.uniformOfFintype K) H ε)
    {B : ProbComp (List M)} {Q : ℕ} (hB : ∀ ms ∈ (ProbComp.eval B).support, ms.length ≤ Q) :
    ProbComp.eval (multiQueryExperiment H B) true ≤ (Q.choose 2 : ℕ) * ε := by
  simp only [multiQueryExperiment, ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure]
  refine Probability.PMF.bind_apply_le_on_support _ fun ms hms => ?_
  rw [Probability.PMF.bind_pure_decide_apply_true]
  refine ((PMF.uniformOfFintype K).toOuterMeasure.mono fun k hk => ?_).trans
    ((hH.toOuterMeasure_not_injOn_le ms.toFinset).trans ?_)
  · rcases hk with ⟨m, hm, m', hm', hne, heq⟩
    intro hinj
    exact hne (hinj (List.mem_toFinset.mpr hm) (List.mem_toFinset.mpr hm') heq)
  · gcongr
    exact ms.toFinset_card_le.trans (hB ms hms)

end Cslib.Crypto.UHF
