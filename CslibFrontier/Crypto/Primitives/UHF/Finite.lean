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
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.PMF.UniformPoint
import Mathlib.Data.List.MinMax

/-!
# Universal hash games with a finite key space

These experiments express the collision and difference-prediction advantages of
[BonehShoup2023], Attack Games 7.1–7.3, as probabilities of returning `true`. The challenger
keeps the uniform key private. An adversary is a closed probabilistic program with no key input.

## Main definitions

* `Cslib.Crypto.UHF.collisionExperiment`: the single-pair collision game (Attack Game 7.1).
* `Cslib.Crypto.UHF.multiQueryExperiment`: the multi-query collision game (Attack Game 7.2).
* `Cslib.Crypto.UHF.differenceExperiment`: the difference-prediction game (Attack Game 7.3).
* `Cslib.Crypto.UHF.bestCollisionGuess`: exhaustive search for a pair with maximal collision
  probability in an enumeration of the message space.

## Main results

* `Cslib.Crypto.UHF.isUniversalHash_iff_eval_collisionExperiment_le` and
  `Cslib.Crypto.UHF.isDeltaUniversalHash_iff_eval_differenceExperiment_le`: the pairwise
  predicates are equivalent to bounding the corresponding advantage for every adversary.
* `Cslib.Crypto.UHF.bestCollisionGuess_wins`: exhaustive search finds a guess that exceeds
  the proposed bound whenever a distinct pair does (Exercise 7.3).
* `Cslib.Crypto.UHF.eval_multiQueryExperiment_le`: the statistical `C(Q, 2) * ε` bound
  for lists of length at most `Q`.

The results here concern one key distribution and one hash function at a time. Computational
security for efficient adversary families and the computational reduction of Lemma 7.1 are
tracked in #5790.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Sections 7.1 and 7.4 and Exercise 7.3.
-/

public section

namespace Cslib.Crypto.UHF

open Cslib.Probability
open scoped ENNReal

variable {K M Y : Type}

/-- The two messages submitted to the collision game. -/
structure CollisionGuess (M : Type) where
  /-- The first message. -/
  first : M
  /-- The second message. -/
  second : M

/-- The messages and the predicted difference of their hashes. -/
structure DifferenceGuess (M Y : Type) extends CollisionGuess M where
  /-- The predicted hash of the second message minus the hash of the first. -/
  difference : Y

/-- Attack Game 7.1 ([BonehShoup2023], v0.6, §7.1, p. 253). A guess wins when its two
distinct messages hash to the same value under an independently sampled uniform key.
The experiment rejects equal messages, which the source forbids submitting. -/
@[expose] noncomputable def collisionExperiment [Fintype K] [Nonempty K] [DecidableEq M]
    [DecidableEq Y] (H : K → M → Y) (A : ProbComp (CollisionGuess M)) : ProbComp Bool := do
  let guess ← A
  let k ← ProbComp.uniform K
  return decide (guess.first ≠ guess.second ∧ H k guess.first = H k guess.second)

/-- Attack Game 7.3 ([BonehShoup2023], v0.6, §7.4, p. 268). A guess wins when its prediction
equals the hash of the second message minus the hash of the first under a uniform key.
Equal messages are rejected. The digest space may be any additive group, encompassing
the source's cyclic group and the XOR example in Remark 7.3. -/
@[expose] noncomputable def differenceExperiment [Fintype K] [Nonempty K] [DecidableEq M]
    [AddGroup Y] [DecidableEq Y] (H : K → M → Y) (A : ProbComp (DifferenceGuess M Y)) :
    ProbComp Bool := do
  let guess ← A
  let k ← ProbComp.uniform K
  return decide (guess.first ≠ guess.second ∧
    H k guess.second - H k guess.first = guess.difference)

private theorem forall_eval_uniformGuess_le_iff {Guess : Type} [Fintype K] [Nonempty K]
    (legal : Guess → Prop) [DecidablePred legal] (wins : Guess → K → Prop)
    [∀ guess, DecidablePred (wins guess)] (ε : ℝ≥0∞) :
    (∀ A : ProbComp Guess, ((ProbComp.eval A).bind fun guess =>
      (PMF.uniformOfFintype K).bind fun k =>
        PMF.pure (decide (legal guess ∧ wins guess k))) true ≤ ε) ↔
      ∀ guess, legal guess → (PMF.uniformOfFintype K).toOuterMeasure {k | wins guess k} ≤ ε := by
  constructor
  · intro h guess hlegal
    simpa only [ProbComp.eval_pure, PMF.pure_bind, hlegal, true_and,
      Probability.PMF.bind_pure_decide_apply_true] using h (pure guess)
  · intro h A
    refine Probability.PMF.bind_apply_le_on_support _ fun guess _ => ?_
    rw [Probability.PMF.bind_pure_decide_apply_true]
    by_cases hlegal : legal guess
    · simpa only [hlegal, true_and] using h guess hlegal
    · simp [hlegal]

/-- The pairwise collision bound (7.1) is equivalent to the game bound of Definition 7.2
([BonehShoup2023], v0.6, p. 254), for one uniform-key instance and any `ε`. -/
theorem isUniversalHash_iff_eval_collisionExperiment_le [Fintype K] [Nonempty K]
    [DecidableEq M] [DecidableEq Y] (H : K → M → Y) (ε : ℝ≥0∞) :
    IsUniversalHash (PMF.uniformOfFintype K) H ε ↔
      ∀ A, ProbComp.eval (collisionExperiment H A) true ≤ ε := by
  simp only [collisionExperiment, ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure]
  rw [forall_eval_uniformGuess_le_iff]
  exact ⟨fun h guess hne => h guess.first guess.second hne, fun h m m' hne => h ⟨m, m'⟩ hne⟩

/-- The pairwise difference bound is equivalent to the game bound of Definition 7.5
([BonehShoup2023], v0.6, pp. 268–269), for one uniform-key instance and any `ε`. -/
theorem isDeltaUniversalHash_iff_eval_differenceExperiment_le [Fintype K] [Nonempty K]
    [DecidableEq M] [AddGroup Y] [DecidableEq Y] (H : K → M → Y) (ε : ℝ≥0∞) :
    IsDeltaUniversalHash (PMF.uniformOfFintype K) H ε ↔
      ∀ A, ProbComp.eval (differenceExperiment H A) true ≤ ε := by
  simp only [differenceExperiment, ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure]
  rw [forall_eval_uniformGuess_le_iff]
  exact ⟨fun h guess hne => h guess.second guess.first hne.symm guess.difference,
    fun h m m' hne d => h ⟨⟨m', m⟩, d⟩ hne.symm⟩

/-- Exhaustively score the distinct pairs from an enumerated message space by the number of
keys giving a collision. Choose the first maximizer, or return `none` if there is no pair. -/
@[expose] def bestCollisionGuess [Fintype K] [DecidableEq M] [DecidableEq Y]
    (H : K → M → Y) (messages : List M) : Option (CollisionGuess M) :=
  let candidates := (messages.product messages).filter fun p => decide (p.1 ≠ p.2)
  let score := fun p : M × M => (Finset.univ.filter fun k => H k p.1 = H k p.2).card
  (candidates.argmax score).map fun p => ⟨p.1, p.2⟩

private theorem eval_collisionExperiment_pure [Fintype K] [Nonempty K] [DecidableEq M]
    [DecidableEq Y] (H : K → M → Y) (guess : CollisionGuess M)
    (hne : guess.first ≠ guess.second) :
    ProbComp.eval (collisionExperiment H (pure guess)) true =
      (PMF.uniformOfFintype K).toOuterMeasure {k | H k guess.first = H k guess.second} := by
  simp only [collisionExperiment, ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure,
    PMF.pure_bind, Probability.PMF.bind_pure_decide_apply_true]
  congr 1
  ext k
  simp [hne]

/-- **Exercise 7.3** ([BonehShoup2023], v0.6, p. 277). Given a complete enumeration of a finite
message space, exhaustive search produces a deterministic guess that exceeds `ε` whenever
some distinct pair does. The search takes only the hash and the enumeration as inputs.
The witness pair and the sampled challenge key are absent from its inputs. -/
theorem bestCollisionGuess_wins [Fintype K] [Nonempty K] [DecidableEq M] [DecidableEq Y]
    (H : K → M → Y) (messages : List M) (complete : ∀ m, m ∈ messages) {ε : ℝ≥0∞}
    {m m' : M} (hne : m ≠ m')
    (h : ε < (PMF.uniformOfFintype K).toOuterMeasure {k | H k m = H k m'}) :
    ∃ guess, bestCollisionGuess H messages = some guess ∧
      ε < ProbComp.eval (collisionExperiment H (pure guess)) true := by
  let candidates := (messages.product messages).filter fun p => decide (p.1 ≠ p.2)
  let score := fun p : M × M => (Finset.univ.filter fun k => H k p.1 = H k p.2).card
  have hmem : (m, m') ∈ candidates := by
    simp [candidates, complete, hne]
  cases hbest : candidates.argmax score with
  | none =>
    rw [List.argmax_eq_none.mp hbest] at hmem
    simp at hmem
  | some p =>
    have hp : p ∈ candidates.argmax score := by simp [hbest]
    have hne' : p.1 ≠ p.2 :=
      of_decide_eq_true (List.mem_filter.mp (List.argmax_mem hp)).2
    have hscore := List.le_of_mem_argmax hmem hp
    refine ⟨⟨p.1, p.2⟩, ?_, ?_⟩
    · change (candidates.argmax score).map (fun q => CollisionGuess.mk q.1 q.2) = _
      simp [hbest]
    · rw [eval_collisionExperiment_pure H _ hne',
        Probability.PMF.toOuterMeasure_uniformOfFintype]
      rw [Probability.PMF.toOuterMeasure_uniformOfFintype] at h
      refine h.trans_le ?_
      change (↑(score (m, m')) : ℝ≥0∞) * (Fintype.card K : ℝ≥0∞)⁻¹ ≤
        (↑(score p) : ℝ≥0∞) * (Fintype.card K : ℝ≥0∞)⁻¹
      exact mul_le_mul' (by exact_mod_cast hscore) le_rfl

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
