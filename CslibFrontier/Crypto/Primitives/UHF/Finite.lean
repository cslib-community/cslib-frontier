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
import CslibFrontier.Probability.PMF.SupportTsum
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
* `Cslib.Crypto.UHF.collisionPairReduction`: turns a list of guesses into one pair.
* `Cslib.Crypto.UHF.bestCollisionGuess`: exhaustive search for a pair with maximal collision
  probability in an enumeration of the message space.

## Main results

* `Cslib.Crypto.UHF.isUniversalHash_iff_eval_collisionExperiment_le` and
  `Cslib.Crypto.UHF.isDeltaUniversalHash_iff_eval_differenceExperiment_le`: the pairwise
  predicates are equivalent to bounding the corresponding advantage for every adversary.
* `Cslib.Crypto.UHF.bestCollisionGuess_wins`: exhaustive search finds a guess that exceeds
  the proposed bound whenever a distinct pair does (Exercise 7.3).
* `Cslib.Crypto.UHF.eval_multiQueryExperiment_le_collisionPairReduction`: the finite-game
  advantage bound for the explicit wrapper, using ideal uniform index draws.
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

private noncomputable def sampleCollisionPair (fallback : M) (ms : List M) :
    ProbComp (CollisionGuess M) :=
  if h : ms = [] then pure ⟨fallback, fallback⟩ else
    haveI : NeZero ms.length := ⟨fun hlen => h (List.length_eq_zero_iff.mp hlen)⟩
    do
      let ij ← ProbComp.uniform (Fin ms.length × Fin ms.length)
      return ⟨ms[ij.1.val], ms[ij.2.val]⟩

/-- Run the multi-query adversary and sample two positions independently and uniformly from its
list. Repeated messages lose in Attack Game 7.1. An empty list gives the repeated dummy message.
The index sampler is ideal. -/
noncomputable def collisionPairReduction (fallback : M) (A : ProbComp (List M)) :
    ProbComp (CollisionGuess M) := do
  let ms ← A
  sampleCollisionPair fallback ms

private theorem collision_indicator_le_samplePair [DecidableEq M] [DecidableEq Y]
    (H : K → M → Y) (k : K) (fallback : M) (ms : List M) {Q : ℕ} (hlen : ms.length ≤ Q) :
    PMF.pure (decide (∃ m ∈ ms, ∃ m' ∈ ms, m ≠ m' ∧ H k m = H k m')) true ≤
      ((Q : ℝ≥0∞) ^ 2 / 2) * ((ProbComp.eval (sampleCollisionPair fallback ms)).bind
        fun g => PMF.pure (decide (g.first ≠ g.second ∧ H k g.first = H k g.second))) true := by
  classical
  by_cases h : ∃ m ∈ ms, ∃ m' ∈ ms, m ≠ m' ∧ H k m = H k m'
  · have hnil : ms ≠ [] := by
      rintro rfl
      simp at h
    have : NeZero ms.length := ⟨fun hlen => hnil (List.length_eq_zero_iff.mp hlen)⟩
    have hcollision := h
    rcases h with ⟨m, hm, m', hm', hne, hd⟩
    obtain ⟨i, hi, hi'⟩ := List.mem_iff_getElem.mp hm
    obtain ⟨j, hj, hj'⟩ := List.mem_iff_getElem.mp hm'
    let a : Fin ms.length := ⟨i, hi⟩
    let b : Fin ms.length := ⟨j, hj⟩
    have hab : a ≠ b := by
      intro he
      have hget := congrArg (fun t : Fin ms.length => ms[t.val]) he
      exact hne (hi'.symm.trans (hget.trans hj'))
    simp only [hcollision, decide_true, PMF.pure_apply_self, sampleCollisionPair,
      dite_eq_right hnil, ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure,
      PMF.bind_bind,
      PMF.pure_bind, Probability.PMF.bind_pure_decide_apply_true]
    let wins (ij : Fin ms.length × Fin ms.length) :=
      ms[ij.1.val] ≠ ms[ij.2.val] ∧ H k ms[ij.1.val] = H k ms[ij.2.val]
    let winning := Finset.univ.filter wins
    have hcard : 2 ≤ winning.card := by
      rw [← Finset.card_pair (a := (a, b)) (b := (b, a)) (by simp [hab])]
      refine Finset.card_le_card fun ij hmem => ?_
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl
      · simp [winning, wins, a, b, hi', hj', hne, hd]
      · simp [winning, wins, a, b, hi', hj', hne.symm, hd.symm]
    rw [Probability.PMF.toOuterMeasure_uniformOfFintype]
    change 1 ≤ ((Q : ℝ≥0∞) ^ 2 / 2) * (winning.card *
      (Fintype.card (Fin ms.length × Fin ms.length) : ℝ≥0∞)⁻¹)
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    rw [← pow_two]
    have hpos : (ms.length : ℝ≥0∞) ^ 2 ≠ 0 :=
      pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne _))
    have hfin : (ms.length : ℝ≥0∞) ^ 2 ≠ ⊤ :=
      ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
    calc
      1 = (((ms.length : ℝ≥0∞) ^ 2) / 2) * (2 * ((ms.length : ℝ≥0∞) ^ 2)⁻¹) := by
        rw [div_eq_mul_inv]
        symm
        calc
          _ = (2 * 2⁻¹) * (((ms.length : ℝ≥0∞) ^ 2) * ((ms.length : ℝ≥0∞) ^ 2)⁻¹) := by
            ring
          _ = 1 := by
            rw [ENNReal.mul_inv_cancel hpos hfin,
              ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]
      _ ≤ _ := by
        gcongr
        exact_mod_cast hcard
  · simp [h]

/-- A finite-game step toward Lemma 7.1 ([BonehShoup2023], v0.6, printed pp. 254–255).
If the multi-query adversary outputs at most `Q` messages, its collision probability is at most
`Q ^ 2 / 2` times that of the explicit single-pair wrapper. Whenever the list contains a
collision, both orders of a colliding pair can be drawn. This argument uses ideal uniform
index draws for one uniform-key instance. The computational-family conclusion of Lemma 7.1
also needs a polynomial-time implementation of the index sampler and wrapper (#5790). -/
theorem eval_multiQueryExperiment_le_collisionPairReduction [Fintype K] [Nonempty K]
    [DecidableEq M] [DecidableEq Y] (H : K → M → Y) (fallback : M)
    (A : ProbComp (List M)) {Q : ℕ} (hA : ∀ ms ∈ (ProbComp.eval A).support, ms.length ≤ Q) :
    ProbComp.eval (multiQueryExperiment H A) true ≤ ((Q : ℝ≥0∞) ^ 2 / 2) *
      ProbComp.eval (collisionExperiment H (collisionPairReduction fallback A)) true := by
  simp only [multiQueryExperiment, collisionExperiment, collisionPairReduction,
    ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform, PMF.bind_bind]
  rw [PMF.bind_apply, PMF.bind_apply, ← ENNReal.tsum_mul_left]
  simp_rw [mul_left_comm ((Q : ℝ≥0∞) ^ 2 / 2)]
  refine Probability.PMF.tsum_mul_mono_support _ fun ms hms => ?_
  rw [PMF.bind_comm (ProbComp.eval (sampleCollisionPair fallback ms)), PMF.bind_apply,
    PMF.bind_apply, ← ENNReal.tsum_mul_left]
  refine tsum_le_tsum fun k => ?_
  rw [mul_left_comm]
  gcongr
  exact collision_indicator_le_samplePair H k fallback ms (hA ms hms)

/-- The `ε`-bounded case of [BonehShoup2023], Lemma 7.1, a step toward the lemma, not the cited
result: against an `ε`-bounded UHF (`IsUniversalHash` for the uniform key, the `ε`-UHF of
Definition 7.2), an adversary whose supported output lists have length at most `Q` wins Attack
Game 7.2 with probability at most `Q.choose 2 * ε`. Only the key type has to be finite. Lemma 7.1
assumes only a computational UHF and bounds the multi-query advantage by `Q ^ 2 / 2` times the
advantage of an efficient wrapper in Attack Game 7.1; here the hash is `ε`-bounded against every
adversary, efficient or not, for one fixed instance, with any `ε` (Definition 7.2 calls it
statistical only when `ε` is negligible), and the proof uses a union bound (#5790). -/
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
